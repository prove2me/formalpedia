-- Prove2me | solution 3 for GrothendieckConstant.grothendieckConst_le_cubic_quintic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T21:44:57.89893+00:00
-- url     : https://prove2.me/submissions/ec9bdcef-eb9b-422d-82b0-ac548e487fb3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckLB_Supplement_cq_eighth_derivative_le_angular_jets
import Theorems.Thm_GrothendieckLB_Supplement_cq_angular_jet_panel_budget
import Theorems.Thm_GrothendieckLB_Supplement_gauss_four_panel_upper_error
import Theorems.Thm_GrothendieckLB_Supplement_cq_energy_gauss_node_sum
import Theorems.Thm_GrothendieckLB_Supplement_cq_energy_panels_smooth
import Mathlib
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_trace_fourier_coefficients
import Theorems.Thm_GrothendieckLB_Supplement_cq_boundary_trace_mean_square
import Mathlib.Analysis.Real.Pi.Bounds
import Theorems.Thm_GrothendieckLB_Supplement_cq_head_coefficient_enclosures
import Theorems.Thm_GrothendieckLB_Supplement_exists_limitingScheme_cqCorr
import Theorems.Thm_GrothendieckLB_Supplement_limitingScheme_bound_of_coefficient_gap
import Mathlib.Analysis.Complex.Exponential

namespace CubicQuinticRemainder

open GrothendieckLB.Supplement CQBoundary

theorem bound :
    ∃ B : ℕ → ℝ, (∀ i < 1024, ∀ x ∈ Set.Icc (0:ℝ) 1,
      iteratedDeriv 8 (GaussFour.panel i) x ≤ B i) ∧
      (∑ i ∈ Finset.range 1024, B i/1778112000)/1024 ≤ 2.29513648 := by
  obtain ⟨V,hV,hbudget⟩ := cq_angular_jet_panel_budget
  refine ⟨fun i => (Real.pi/1024)^8*jetMajorant (V i),?_,hbudget⟩
  intro i hi x hx
  let θ := (i:ℝ)*(Real.pi/1024)+(Real.pi/1024)*x
  apply (cq_eighth_derivative_le_angular_jets i x).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold jetMajorant
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ 8 := by have h := Finset.mem_range.mp hj; omega
  have h8 : 8-j ≤ 8 := Nat.sub_le .. 
  have hn (b k) : 0 ≤ angularJetNorm b k θ := Real.sqrt_nonneg _
  have hp (b : Bool) : angularJetNorm b j θ * angularJetNorm b (8-j) θ ≤ V i b j * V i b (8-j) :=
    mul_le_mul (hV i hi x hx b j hj') (hV i hi x hx b (8-j) h8) (hn ..)
      ((hn ..).trans (hV i hi x hx b j hj'))
  exact mul_le_mul_of_nonneg_left (add_le_add (hp false)
    (mul_le_mul_of_nonneg_left (hp true) (by norm_num))) (Nat.cast_nonneg _)

end CubicQuinticRemainder

namespace CubicQuinticQuadrature

open GrothendieckLB.Supplement CQBoundary GaussFour MeasureTheory

theorem bound :
    Real.pi⁻¹ * (∫ θ in (0:ℝ)..Real.pi, CQBoundary.energy θ) ≤ 126.80385221 := by
  let D : ℝ := Real.pi/1024
  let a (i : ℕ) : ℝ := (i:ℝ)*D
  have hD : D ≠ 0 := div_ne_zero Real.pi_ne_zero (by norm_num)
  have hcts : Continuous energy := by
    have he : energy = fun t : ℝ => panel 0 (t/D) := by
      funext t
      unfold panel
      simp only [Nat.cast_zero,zero_mul,zero_add]
      congr 1
      change t=D*(t/D)
      field_simp
    rw [he]
    exact (cq_energy_panels_smooth 0).continuous.comp (continuous_id.div_const D)
  have eqpanel (i : ℕ) : D*(∫ x in (0:ℝ)..1, panel i x) = ∫ θ in a i..a (i+1), energy θ := by
    have h := intervalIntegral.smul_integral_comp_add_mul (a:=(0:ℝ)) (b:=1) energy D (a i)
    change D*(∫ x in (0:ℝ)..1, energy (a i+D*x)) = ∫ θ in a i+D*0..a i+D*1, energy θ at h
    rw [mul_zero,add_zero,mul_one] at h
    simpa only [panel,a,Nat.cast_add,Nat.cast_one,add_mul,one_mul,D] using h
  have he : D*(∑ i ∈ Finset.range 1024, ∫ x in (0:ℝ)..1, panel i x)=∫ θ in (0:ℝ)..Real.pi, energy θ := by
    rw [Finset.mul_sum]
    simp_rw [eqpanel]
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hcts.intervalIntegrable (a k) (a (k+1)))]
    have hp : a 1024=Real.pi := by dsimp [a,D]; ring
    rw [hp,show a 0=0 by simp [a]]
  obtain ⟨B,hB,hrem⟩ := CubicQuinticRemainder.bound
  have hsum := Finset.sum_le_sum (s:=Finset.range 1024) (fun i hi =>
    gauss_four_panel_upper_error (panel i) (B i) (cq_energy_panels_smooth i) (hB i (Finset.mem_range.mp hi)))
  rw [Finset.sum_add_distrib] at hsum
  have hnorm : Real.pi⁻¹*(∫ θ in (0:ℝ)..Real.pi, energy θ)=
      (∑ i ∈ Finset.range 1024, ∫ x in (0:ℝ)..1, panel i x)/1024 := by
    rw [←he,←mul_assoc]
    dsimp [D]
    field_simp
  rw [hnorm]
  linarith only [hsum,hrem,cq_energy_gauss_node_sum]

end CubicQuinticQuadrature

namespace CubicQuinticTail

open MeasureTheory GrothendieckLB GrothendieckLB.Supplement

private theorem odd_mode_bessel (f : ℝ → ℂ) (b : ℕ → ℝ)
    (hab : (0:ℝ) < 2*Real.pi) (h2 : MemLp f 2 (volume.restrict (Set.Ioc 0 (2*Real.pi))))
    (hw : ∀ m : ℕ, fourierCoeffOn hab f (m:ℤ) = (m:ℂ)^3 * (b m : ℂ)) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((251:ℝ)+2*((j:ℝ)+1))^6 * (b (2*j+253))^2) ≤
      (2*Real.pi)⁻¹ * ∫ θ in (0:ℝ)..2*Real.pi, ‖f θ‖^2 := by
  let e : ℕ ↪ ℤ := ⟨fun j => ((2*j+253:ℕ):ℤ), fun i j h => by dsimp at h; omega⟩
  have P := hasSum_sq_fourierCoeffOn hab h2
  have B := P.summable.sum_le_tsum ((Finset.range n).map e)
    (fun i _ => sq_nonneg ‖fourierCoeffOn hab f i‖)
  rw [P.tsum_eq,sub_zero,smul_eq_mul,Finset.sum_map] at B
  apply le_trans ?_ B
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro j _
  change _ = ‖fourierCoeffOn hab f ((2*j+253:ℕ):ℤ)‖^2
  rw [hw, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]
  push_cast
  ring

theorem bound :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    ∀ n : ℕ, (∑ j ∈ Finset.range n,
      ((251 : ℝ) + 2 * ((j : ℝ) + 1)) ^ 6 *
        (taylorCoeff (2 * j + 253) H) ^ 2) ≤ (14.443 : ℝ) ^ 2 := by
  obtain ⟨hm,hf⟩ := cq_boundary_trace_fourier_coefficients
  dsimp only
  intro n
  refine (odd_mode_bessel _ _ (by positivity) hm hf n).trans (cq_boundary_trace_mean_square.trans ?_)
  calc
    _ ≤ Real.pi^2 / 6 * 126.80385221 :=
      mul_le_mul_of_nonneg_left CubicQuinticQuadrature.bound (by positivity)
    _ ≤ 14.443^2 := by
      have hp := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d4.le 2
      linarith only [hp]

end CubicQuinticTail

namespace CubicQuinticCoefficients

open GrothendieckLB GrothendieckLB.Supplement

private theorem reciprocal_sixth_step (x : ℝ) (hx : 0 < x) :
    1 / (x + 2) ^ 6 ≤ 1 / (10 * x ^ 5) - 1 / (10 * (x + 2) ^ 5) := by
  have hp : 10 * x ^ 5 + x ^ 5 * (x + 2) ≤ (x + 2) ^ 6 := by
    have h : 0 ≤ 60 * x^4 + 160 * x^3 + 240 * x^2 + 192 * x + 64 := by positivity
    nlinarith only [h]
  apply (le_sub_iff_add_le).2
  apply sub_nonneg.mp
  have hden : x + 2 ≠ 0 := by positivity
  have hid :
      1 / (10 * x ^ 5) - (1 / (x + 2) ^ 6 + 1 / (10 * (x + 2) ^ 5)) =
        ((x + 2) ^ 6 - (10 * x ^ 5 + x ^ 5 * (x + 2))) / (10 * x ^ 5 * (x + 2) ^ 6) := by
    field_simp [hx.ne', hden] <;> ring
  rw [hid]
  exact div_nonneg (sub_nonneg.mpr hp) (by positivity)

private theorem reciprocal_sixth_sum (N : ℝ) (hN : 0 < N) (k : ℕ) :
    (∑ j ∈ Finset.range k, 1 / (N + 2 * ((j : ℝ) + 1)) ^ 6) ≤
      1 / (10 * N ^ 5) - 1 / (10 * (N + 2 * (k : ℝ)) ^ 5) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h := reciprocal_sixth_step (N + 2 * (k : ℝ)) (by positivity)
    rw [show N + 2 * (k : ℝ) + 2 = N + 2 * ((k : ℝ) + 1) by ring] at h
    linarith only [ih, h]

private theorem odd_tail_from_square_sums (a : ℕ → ℝ) (N B : ℝ) (hN : 0 < N) (hB : 0 ≤ B)
    (hw : ∀ k, (∑ j ∈ Finset.range k, (N + 2 * ((j : ℝ) + 1)) ^ 6 * (a j) ^ 2) ≤ B ^ 2) :
    Summable (fun j => |a j|) ∧ (∑' j, |a j|) ≤ B / Real.sqrt (10 * N ^ 5) := by
  let L (j : ℕ) : ℝ := N + 2 * ((j : ℝ) + 1)
  have hL (j : ℕ) : 0 < L j := by dsimp [L]; positivity
  have hbound (k : ℕ) : (∑ j ∈ Finset.range k, |a j|) ≤ B / Real.sqrt (10 * N ^ 5) := by
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.range k)
      (r := fun j => |a j|) (f := fun j => (L j)^6 * (a j)^2) (g := fun j => 1 / (L j)^6)
      (fun j _ => mul_nonneg (pow_nonneg (hL j).le _) (sq_nonneg _))
      (fun j _ => div_nonneg zero_le_one (pow_nonneg (hL j).le _))
      (fun j _ => by rw [sq_abs]; apply le_of_eq; field_simp [(hL j).ne'] <;> ring)
    have hrec : (∑ j ∈ Finset.range k, 1 / (L j)^6) ≤ 1 / (10 * N^5) :=
      (reciprocal_sixth_sum N hN k).trans (sub_le_self _ (by positivity))
    have hs : (∑ j ∈ Finset.range k, |a j|)^2 ≤ B^2 * (1/(10*N^5)) :=
      hcs.trans (mul_le_mul (hw k) hrec
        (Finset.sum_nonneg fun j _ => div_nonneg zero_le_one (pow_nonneg (hL j).le _))
        (sq_nonneg B))
    have hden : 0 ≤ 10 * N^5 := by positivity
    have hid : (B / Real.sqrt (10 * N^5))^2 = B^2 * (1/(10*N^5)) := by
      rw [div_pow, Real.sq_sqrt hden]
      ring
    rw [← hid] at hs
    exact (sq_le_sq₀ (Finset.sum_nonneg fun j _ => abs_nonneg (a j))
      (div_nonneg hB (Real.sqrt_nonneg _))).mp hs
  exact ⟨summable_of_sum_range_le (fun j => abs_nonneg (a j)) hbound,
    Real.tsum_le_of_sum_range_le (fun j => abs_nonneg (a j)) hbound⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
private theorem head_units_sum :
    (∑ j ∈ Finset.range 125, cqHeadUnits[j]?.getD 0) = 1132885992769046 := by
  decide +kernel

theorem bound :
    let H := cqCorr 0.136419125 0.34101124 0.05276111
    let b := fun m : ℕ => taylorCoeff m H
    0.881573822049 ≤ b 1 ∧
      (∑ j ∈ Finset.range 125, |b (2 * j + 3)|) ≤ 0.000011328860 ∧
      Summable (fun j : ℕ => |b (2 * j + 253)|) ∧
      (∑' j : ℕ, |b (2 * j + 253)|) ≤ 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let b (m : ℕ) := taylorCoeff m H
  obtain ⟨h1, hodd⟩ := cq_head_coefficient_enclosures
  refine ⟨le_trans (by norm_num : (0.881573822049 : ℝ) ≤ 88157382204959954858 / 10^20) h1, ?_, ?_⟩
  · calc
      (∑ j ∈ Finset.range 125, |b (2*j+3)|) ≤
          ∑ j ∈ Finset.range 125, ((cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10^20 :=
        Finset.sum_le_sum fun j hj => hodd j (Finset.mem_range.mp hj)
      _ = ((∑ j ∈ Finset.range 125, cqHeadUnits[j]?.getD 0 : ℕ) : ℝ) / 10^20 := by
        rw [← Finset.sum_div, Nat.cast_sum]
      _ ≤ 0.000011328860 := by rw [head_units_sum]; norm_num
  · exact odd_tail_from_square_sums (fun j => b (2*j+253)) 251 14.443
      (by norm_num) (by norm_num) CubicQuinticTail.bound

end CubicQuinticCoefficients

open GrothendieckConstant GrothendieckLB GrothendieckLB.Supplement

set_option maxHeartbeats 800000 in
private theorem compare_cubic_quintic_constant :
    Real.pi / (2 * 0.881545409) ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  have hsqrt : Real.sqrt 2 ≤ 1.414213563 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hexp : (2.414213563 : ℝ) ≤ Real.exp 0.8813736 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 11, (0.8813736 : ℝ) ^ j / j.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ _ := Real.sum_le_exp_of_nonneg (by norm_num) 11
  have hlog : Real.log (1 + Real.sqrt 2) ≤ 0.8813736 := by
    apply (Real.log_le_iff_le_exp (by positivity)).2
    linarith only [hsqrt, hexp]
  have hlog_pos : 0 < Real.log (1 + Real.sqrt 2) := by
    apply Real.log_pos
    have h := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hdiv : Real.pi / (2 * 0.8813736) ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by positivity) (by linarith only [hlog])
  calc
    Real.pi / (2 * 0.881545409) ≤ Real.pi / (2 * 0.8813736) - 3.47 * 10 ^ (-4 : ℤ) := by
      norm_num [div_eq_mul_inv] <;> linarith only [Real.pi_gt_d2]
    _ ≤ _ := sub_le_sub_right hdiv _

theorem solution :
    grothendieckConst ≤
      Real.pi / (2 * Real.log (1 + Real.sqrt 2)) - 3.47 * 10 ^ (-4 : ℤ) := by
  let H := cqCorr 0.136419125 0.34101124 0.05276111
  let a (j : ℕ) := |taylorCoeff (2 * j + 3) H|
  obtain ⟨S, hS⟩ := exists_limitingScheme_cqCorr 0.136419125 0.34101124 0.05276111
  change S.corr = H at hS
  obtain ⟨hlinear, hhead, htail_sum, htail⟩ := CubicQuinticCoefficients.bound
  change 0.881573822049 ≤ taylorCoeff 1 H at hlinear
  change (∑ j ∈ Finset.range 125, a j) ≤ 0.000011328860 at hhead
  have hshift (j : ℕ) : a (j + 125) = |taylorCoeff (2 * j + 253) H| := by
    dsimp only [a]
    rw [show 2 * (j + 125) + 3 = 2 * j + 253 by omega]
  have hsum : Summable a := by
    apply (summable_nat_add_iff (f := a) 125).1
    simpa only [hshift] using htail_sum
  have hsqrt : (14.443 / 0.000004575864 : ℝ) ≤ Real.sqrt (10 * (251 : ℝ) ^ 5) :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have htail_num : 14.443 / Real.sqrt (10 * (251 : ℝ) ^ 5) ≤ 0.000004575864 := by
    apply (div_le_iff₀ (by positivity)).2
    simpa only [mul_comm] using
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 0.000004575864)).mp hsqrt
  have hmass : (∑' j, a j) ≤ 0.000015904724 := by
    rw [← hsum.sum_add_tsum_nat_add 125]
    have htail' : (∑' j : ℕ, a (j + 125)) ≤ 0.000004575864 := by
      simpa only [hshift] using htail.trans htail_num
    linarith only [hhead, htail']
  have hgap : 0.881545409 + (∑' j, a j) < taylorCoeff 1 H := by
    linarith only [hmass, hlinear]
  refine le_trans ?_ compare_cubic_quintic_constant
  apply limitingScheme_bound_of_coefficient_gap S 0.881545409 (by norm_num)
  · rw [hS]
    exact hsum
  · rw [hS]
    exact hgap

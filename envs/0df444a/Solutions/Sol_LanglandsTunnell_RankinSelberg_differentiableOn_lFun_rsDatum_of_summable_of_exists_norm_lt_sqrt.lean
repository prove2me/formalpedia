-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/36032dc2-e323-5913-bcb1-9026aa9b1145

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_LanglandsTunnell_RankinSelberg_converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b"

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal
open LanglandsTunnell.RankinSelberg

namespace RankinSelbergHolomorphy
open Polynomial LanglandsTunnell LanglandsTunnell.RankinSelberg

private theorem tprod_eq_zero_of_factor {ι : Type} (g : ι → ℂ) (i₀ : ι) (h : g i₀ = 0) : ∏' i, g i = 0 := by
  refine HasProd.tprod_eq ?_
  refine tendsto_atTop_of_eventually_const (i₀ := {i₀}) fun t ht => ?_
  exact Finset.prod_eq_zero (ht (Finset.mem_singleton_self i₀)) h

private theorem factor_ne_zero_of_tprod_inv_ne_zero {ι : Type} (e : ι → ℂ) (h : ∏' i, (e i)⁻¹ ≠ 0) (i : ι) :
    e i ≠ 0 := by
  intro hi
  exact h (tprod_eq_zero_of_factor (fun j => (e j)⁻¹) i (by simp [hi]))

private theorem differentiableOn_tprod_inv_of_forall_exists_summable {ι : Type} (e : ι → ℂ → ℂ) (σ₀ : ℝ)
    (hdiff : ∀ i, Differentiable ℂ (e i))
    (hne : ∀ s : ℂ, σ₀ < s.re → ∀ i, e i s ≠ 0)
    (hmaj : ∀ σ₁ : ℝ, σ₀ < σ₁ → ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ s : ℂ, σ₁ ≤ s.re → ‖e i s - 1‖ ≤ u i) :
    DifferentiableOn ℂ (fun s => ∏' i, (e i s)⁻¹) {s : ℂ | σ₀ < s.re} := by
  intro s₀ hs₀
  have hs₀' : σ₀ < s₀.re := hs₀
  obtain ⟨u, hu, hbound⟩ := hmaj ((σ₀ + s₀.re) / 2) (by linarith)
  set U : Set ℂ := {s : ℂ | (σ₀ + s₀.re) / 2 < s.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUsub : ∀ s ∈ U, σ₀ < s.re := fun s hs => by
    have hs' : (σ₀ + s₀.re) / 2 < s.re := hs
    linarith
  have hs₀U : s₀ ∈ U := by
    show (σ₀ + s₀.re) / 2 < s₀.re
    linarith

  have hev : ∀ᶠ i in Filter.cofinite, ∀ s ∈ U, ‖(e i s)⁻¹ - 1‖ ≤ 2 * u i := by
    have hhalf : ∀ᶠ i in Filter.cofinite, u i < 1 / 2 :=
      hu.tendsto_cofinite_zero.eventually (gt_mem_nhds (by norm_num))
    filter_upwards [hhalf] with i hi s hs
    have hs' : (σ₀ + s₀.re) / 2 < s.re := hs
    have hes : ‖e i s - 1‖ ≤ u i := hbound i s hs'.le
    have hne' : e i s ≠ 0 := hne s (hUsub s hs) i
    have hehalf : (1 / 2 : ℝ) ≤ ‖e i s‖ := by
      have h1 := (abs_le.mp (abs_norm_sub_norm_le (e i s) 1)).1
      rw [norm_one] at h1
      linarith
    have hrepr : (e i s)⁻¹ - 1 = (1 - e i s) * (e i s)⁻¹ := by
      field_simp
    rw [hrepr, norm_mul, norm_inv, norm_sub_rev]
    have hinv : ‖e i s‖⁻¹ ≤ 2 := by
      have := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hehalf
      norm_num at this
      exact this
    calc ‖e i s - 1‖ * ‖e i s‖⁻¹ ≤ u i * 2 :=
          mul_le_mul hes hinv (inv_nonneg.mpr (norm_nonneg _)) (le_trans (norm_nonneg _) hes)
      _ = 2 * u i := mul_comm _ _
  have hcts : ∀ i, ContinuousOn (fun s => (e i s)⁻¹ - 1) U := fun i =>
    ((hdiff i).continuous.continuousOn.inv₀ fun s hs => hne s (hUsub s hs) i).sub continuousOn_const
  have hprod := Summable.hasProdLocallyUniformlyOn_one_add hUopen (hu.mul_left 2) hev hcts
  have hT := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hfin : ∀ t : Finset ι, DifferentiableOn ℂ (fun s => ∏ i ∈ t, (1 + ((e i s)⁻¹ - 1))) U := fun t =>
    DifferentiableOn.fun_finsetProd fun i _ =>
      (differentiableOn_const _).add
        (((hdiff i).differentiableOn.inv fun s hs => hne s (hUsub s hs) i).sub (differentiableOn_const _))
  have hlim : DifferentiableOn ℂ (fun s => ∏' i, (1 + ((e i s)⁻¹ - 1))) U :=
    hT.differentiableOn (Filter.Eventually.of_forall hfin) hUopen
  have hcongr : DifferentiableOn ℂ (fun s => ∏' i, (e i s)⁻¹) U :=
    hlim.congr fun s _ => by simp
  exact (hcongr.differentiableAt (hUopen.mem_nhds hs₀U)).differentiableWithinAt

section ConvGeneric
open Polynomial Filter Topology

variable {ι : Type*}

private theorem norm_eval_sub_one_le (P : ℂ[X]) {n : ℕ} (hdeg : P.natDegree ≤ n) (h0 : P.coeff 0 = 1)
    (x : ℂ) : ‖P.eval x - 1‖ ≤ ∑ k ∈ Finset.range n, ‖P.coeff (k + 1)‖ * ‖x‖ ^ (k + 1) := by
  have h : P.eval x - 1 = ∑ k ∈ Finset.range n, P.coeff (k + 1) * x ^ (k + 1) := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_range_succ', h0]
    simp
  rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_pow]

private theorem norm_natCast_cpow_neg (q : ℕ) (hq : 0 < q) (s : ℂ) :
    ‖(q : ℂ) ^ (-s)‖ = (q : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]

private theorem norm_natCast_cpow_neg_pow (q : ℕ) (hq : 0 < q) (s : ℂ) (m : ℕ) :
    ‖(q : ℂ) ^ (-s)‖ ^ m = (q : ℝ) ^ (-(s.re * m)) := by
  rw [norm_natCast_cpow_neg q hq s, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q)]
  congr 1
  ring

private theorem summable_norm_eval_sub_one {q : ι → ℕ} {P : ι → ℂ[X]} {n : ℕ} (hq : ∀ i, 0 < q i)
    (hdeg : ∀ i, (P i).natDegree ≤ n) (h0 : ∀ i, (P i).coeff 0 = 1) (s : ℂ)
    (hsum : ∀ k : ℕ, k < n →
      Summable fun i => ‖(P i).coeff (k + 1)‖ * (q i : ℝ) ^ (-(s.re * (k + 1)))) :
    Summable fun i => ‖(P i).eval ((q i : ℂ) ^ (-s)) - 1‖ := by
  refine Summable.of_norm_bounded (g := fun i => ∑ k ∈ Finset.range n,
      ‖(P i).coeff (k + 1)‖ * (q i : ℝ) ^ (-(s.re * (k + 1)))) ?_ ?_
  · exact summable_sum fun k hk => hsum k (Finset.mem_range.mp hk)
  · intro i
    rw [norm_norm]
    refine (norm_eval_sub_one_le (P i) (hdeg i) (h0 i) _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_natCast_cpow_neg_pow (q i) (hq i) s (k + 1), Nat.cast_succ]

end ConvGeneric

section ConvDomination
open Polynomial Filter Topology

variable {ι : Type*}

private theorem rpow_neg_mul_succ (q : ℕ) (σ : ℝ) (k : ℕ) :
    (q : ℝ) ^ (-(σ * (k + 1))) = ((q : ℝ) ^ (-σ)) ^ (k + 1) := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg q) (-σ) (k + 1)]
  congr 1
  push_cast
  ring

private theorem summable_norm_coeff_mul_rpow {q : ι → ℕ} {P : ι → ℂ[X]} {a : ι → ℝ} {C σ : ℝ}
    {n : ℕ} (hC : 0 ≤ C) (ha0 : ∀ i, 0 ≤ a i)
    (hle : ∀ i, ∀ k < n, ‖(P i).coeff (k + 1)‖ ≤ C * (1 + a i) ^ (k + 1))
    (hsum : Summable fun i => (1 + a i) * (q i : ℝ) ^ (-σ)) (k : ℕ) (hk : k < n) :
    Summable fun i => ‖(P i).coeff (k + 1)‖ * (q i : ℝ) ^ (-(σ * (k + 1))) := by
  have hv0 : ∀ i, 0 ≤ (1 + a i) * (q i : ℝ) ^ (-σ) := fun i =>
    mul_nonneg (by linarith [ha0 i]) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have ht : Tendsto (fun i => (1 + a i) * (q i : ℝ) ^ (-σ)) cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, (1 + a i) * (q i : ℝ) ^ (-σ) ∈ Set.Iic (1 : ℝ) :=
    ht.eventually_mem (Iic_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (hsum.mul_left C) ?_
  filter_upwards [hev] with i hi
  have hi' : (1 + a i) * (q i : ℝ) ^ (-σ) ≤ 1 := hi
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))]
  calc ‖(P i).coeff (k + 1)‖ * (q i : ℝ) ^ (-(σ * (k + 1)))
      ≤ C * (1 + a i) ^ (k + 1) * (q i : ℝ) ^ (-(σ * (k + 1))) :=
        mul_le_mul_of_nonneg_right (hle i k hk) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = C * ((1 + a i) * (q i : ℝ) ^ (-σ)) ^ (k + 1) := by
        rw [rpow_neg_mul_succ, mul_pow]
        ring
    _ ≤ C * ((1 + a i) * (q i : ℝ) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left (pow_le_of_le_one (hv0 i) hi' (Nat.succ_ne_zero k)) hC

private theorem summable_one_add_mul_rpow {q : ι → ℕ} {a : ι → ℝ} {σ : ℝ}
    (hq : Summable fun i => (q i : ℝ) ^ (-σ)) (ha : Summable fun i => a i * (q i : ℝ) ^ (-σ)) :
    Summable fun i => (1 + a i) * (q i : ℝ) ^ (-σ) := by
  have h := hq.add ha
  refine h.congr fun i => ?_
  ring

end ConvDomination

section ConvCoefficients
open Polynomial

variable {R : Type*} [CommRing R]

private theorem natDegree_rsEulerPoly_le (a b e₁ e₂ e₃ : R) : (rsEulerPoly a b e₁ e₂ e₃).natDegree ≤ 6 := by
  unfold rsEulerPoly
  compute_degree

private theorem coeff_rsEulerPoly_zero (a b e₁ e₂ e₃ : R) : (rsEulerPoly a b e₁ e₂ e₃).coeff 0 = 1 := by
  simp only [rsEulerPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

private theorem coeff_rsEulerPoly_succ (a b e₁ e₂ e₃ : R) :
    (rsEulerPoly a b e₁ e₂ e₃).coeff 1 = -(a * e₁) ∧
    (rsEulerPoly a b e₁ e₂ e₃).coeff 2 = a ^ 2 * e₂ + b * e₁ ^ 2 - 2 * b * e₂ ∧
    (rsEulerPoly a b e₁ e₂ e₃).coeff 3 = -(a ^ 3 * e₃) - a * b * e₁ * e₂ + 3 * a * b * e₃ ∧
    (rsEulerPoly a b e₁ e₂ e₃).coeff 4 = a ^ 2 * b * e₁ * e₃ - 2 * b ^ 2 * e₁ * e₃ + b ^ 2 * e₂ ^ 2 ∧
    (rsEulerPoly a b e₁ e₂ e₃).coeff 5 = -(a * b ^ 2 * e₂ * e₃) ∧
    (rsEulerPoly a b e₁ e₂ e₃).coeff 6 = b ^ 3 * e₃ ^ 2 := by
  simp only [rsEulerPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  simp

private theorem monomial_le {A E : ℝ} (hA : 0 ≤ A) (hE : 0 ≤ E) {i j m : ℕ} (hi : i ≤ m) (hj : j ≤ 3) :
    A ^ i * E ^ j ≤ (1 + A) ^ m * (E + 1) ^ 3 := by
  have h1 : A ^ i ≤ (1 + A) ^ m :=
    (pow_le_pow_left₀ hA (by linarith) i).trans (pow_le_pow_right₀ (by linarith) hi)
  have h2 : E ^ j ≤ (E + 1) ^ 3 :=
    (pow_le_pow_left₀ hE (by linarith) j).trans (pow_le_pow_right₀ (by linarith) hj)
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

private theorem norm_coeff_rsEulerPoly_succ_le (a b e₁ e₂ e₃ : ℂ) {E : ℝ} (hb : ‖b‖ = 1)
    (h₁ : ‖e₁‖ ≤ E) (h₂ : ‖e₂‖ ≤ E) (h₃ : ‖e₃‖ ≤ E) (hE : 0 ≤ E) :
    ∀ k : ℕ, k < 6 →
      ‖(rsEulerPoly a b e₁ e₂ e₃).coeff (k + 1)‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ (k + 1) := by
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := coeff_rsEulerPoly_succ a b e₁ e₂ e₃
  have hA : 0 ≤ ‖a‖ := norm_nonneg a
  have hE₁ : ‖e₁‖ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
  have hE₂ : ‖e₂‖ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₂ 2
  have hE₃ : ‖e₃‖ ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h₃ 2
  have h₁₂ : ‖e₁‖ * ‖e₂‖ ≤ E ^ 2 := by rw [sq]; exact mul_le_mul h₁ h₂ (norm_nonneg _) hE
  have h₁₃ : ‖e₁‖ * ‖e₃‖ ≤ E ^ 2 := by rw [sq]; exact mul_le_mul h₁ h₃ (norm_nonneg _) hE
  have h₂₃ : ‖e₂‖ * ‖e₃‖ ≤ E ^ 2 := by rw [sq]; exact mul_le_mul h₂ h₃ (norm_nonneg _) hE
  have hP : ∀ m : ℕ, 0 ≤ (1 + ‖a‖) ^ m * (E + 1) ^ 3 := fun m => by positivity
  intro k hk
  interval_cases k
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 1‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 1
    rw [c₁, norm_neg, norm_mul]
    have m1 := monomial_le hA hE (i := 1) (j := 1) (m := 1) le_rfl (by norm_num)
    have : ‖a‖ * ‖e₁‖ ≤ ‖a‖ ^ 1 * E ^ 1 := by
      simp only [pow_one]; exact mul_le_mul_of_nonneg_left h₁ hA
    nlinarith [hP 1]
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 2‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 2
    rw [c₂]
    have hsum := (norm_sub_le (a ^ 2 * e₂ + b * e₁ ^ 2) (2 * b * e₂)).trans
      (add_le_add (norm_add_le (a ^ 2 * e₂) (b * e₁ ^ 2)) le_rfl)
    simp only [norm_mul, norm_pow, hb, one_mul, Complex.norm_ofNat] at hsum
    have t1 : ‖a‖ ^ 2 * ‖e₂‖ ≤ ‖a‖ ^ 2 * E ^ 1 := by
      rw [pow_one]; exact mul_le_mul_of_nonneg_left h₂ (by positivity)
    have m1 := monomial_le hA hE (i := 2) (j := 1) (m := 2) le_rfl (by norm_num)
    have m2 := monomial_le hA hE (i := 0) (j := 2) (m := 2) (by norm_num) (by norm_num)
    have m3 := monomial_le hA hE (i := 0) (j := 1) (m := 2) (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul, pow_one] at m2 m3
    nlinarith [hP 2]
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 3‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 3
    rw [c₃]
    have hsum := (norm_add_le (-(a ^ 3 * e₃) - a * b * e₁ * e₂) (3 * a * b * e₃)).trans
      (add_le_add (norm_sub_le (-(a ^ 3 * e₃)) (a * b * e₁ * e₂)) le_rfl)
    simp only [norm_neg, norm_mul, norm_pow, hb, mul_one, Complex.norm_ofNat] at hsum
    have t1 : ‖a‖ ^ 3 * ‖e₃‖ ≤ ‖a‖ ^ 3 * E ^ 1 := by
      rw [pow_one]; exact mul_le_mul_of_nonneg_left h₃ (by positivity)
    have t2 : ‖a‖ * ‖e₁‖ * ‖e₂‖ ≤ ‖a‖ ^ 1 * E ^ 2 := by
      rw [pow_one, mul_assoc]; exact mul_le_mul_of_nonneg_left h₁₂ hA
    have t3 : 3 * ‖a‖ * ‖e₃‖ ≤ 3 * (‖a‖ ^ 1 * E ^ 1) := by
      simp only [pow_one, mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₃ hA) (by norm_num)
    have m1 := monomial_le hA hE (i := 3) (j := 1) (m := 3) le_rfl (by norm_num)
    have m2 := monomial_le hA hE (i := 1) (j := 2) (m := 3) (by norm_num) (by norm_num)
    have m3 := monomial_le hA hE (i := 1) (j := 1) (m := 3) (by norm_num) (by norm_num)
    nlinarith [hP 3]
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 4‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 4
    rw [c₄]
    have hsum := (norm_add_le (a ^ 2 * b * e₁ * e₃ - 2 * b ^ 2 * e₁ * e₃) (b ^ 2 * e₂ ^ 2)).trans
      (add_le_add (norm_sub_le (a ^ 2 * b * e₁ * e₃) (2 * b ^ 2 * e₁ * e₃)) le_rfl)
    simp only [norm_mul, norm_pow, hb, mul_one, one_pow, one_mul, Complex.norm_ofNat] at hsum
    have t1 : ‖a‖ ^ 2 * ‖e₁‖ * ‖e₃‖ ≤ ‖a‖ ^ 2 * E ^ 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h₁₃ (by positivity)
    have t2 : 2 * ‖e₁‖ * ‖e₃‖ ≤ 2 * E ^ 2 := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h₁₃ (by norm_num)
    have m1 := monomial_le hA hE (i := 2) (j := 2) (m := 4) (by norm_num) (by norm_num)
    have m2 := monomial_le hA hE (i := 0) (j := 2) (m := 4) (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at m2
    nlinarith [hP 4]
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 5‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 5
    rw [c₅, norm_neg]
    simp only [norm_mul, norm_pow, hb, one_pow, mul_one]
    have t : ‖a‖ * ‖e₂‖ * ‖e₃‖ ≤ ‖a‖ ^ 1 * E ^ 2 := by
      rw [pow_one, mul_assoc]; exact mul_le_mul_of_nonneg_left h₂₃ hA
    have m1 := monomial_le hA hE (i := 1) (j := 2) (m := 5) (by norm_num) (by norm_num)
    nlinarith [hP 5]
  ·
    show ‖(rsEulerPoly a b e₁ e₂ e₃).coeff 6‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖a‖) ^ 6
    rw [c₆]
    simp only [norm_mul, norm_pow, hb, one_pow, one_mul]
    have m1 := monomial_le hA hE (i := 0) (j := 2) (m := 6) (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul] at m1
    nlinarith [hP 6]

end ConvCoefficients

section ConvFibre
open Polynomial IsDedekindDomain NumberField

private theorem ringHom_ringOfIntegers_rat_ext' {R : Type*} [Semiring R] (f g : 𝓞 ℚ →+* R) : f = g := by
  have h : f.comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      g.comp Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  ext x
  have hx := RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  rw [RingHom.comp_apply, RingHom.comp_apply] at hx
  have he : Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x) = x :=
    Rat.ringOfIntegersEquiv.symm_apply_apply x
  rwa [he] at hx

private theorem algebra_eq_inst_ringOfIntegersAlgebra' (K : Type) [Field K] [NumberField K]
    (inst : Algebra (𝓞 ℚ) (𝓞 K)) : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
  Algebra.algebra_ext _ _ fun x =>
    RingHom.congr_fun (ringHom_ringOfIntegers_rat_ext' (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ inst)
      (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ K))) x

private theorem ringHom_ringOfIntegers_rat_injective' {R : Type*} [Ring R] [IsDomain R] [CharZero R]
    (f : 𝓞 ℚ →+* R) : Function.Injective f := by
  have h : Function.Injective (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom) :=
    (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom).injective_int
  intro x y hxy
  have h' : (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom) (Rat.ringOfIntegersEquiv x) =
      (f.comp Rat.ringOfIntegersEquiv.symm.toRingHom) (Rat.ringOfIntegersEquiv y) := by
    rw [RingHom.comp_apply, RingHom.comp_apply]
    have hx : Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x) = x :=
      Rat.ringOfIntegersEquiv.symm_apply_apply x
    have hy : Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv y) = y :=
      Rat.ringOfIntegersEquiv.symm_apply_apply y
    rw [hx, hy, hxy]
  exact Rat.ringOfIntegersEquiv.injective (h h')

section Fibre

variable (K : Type) [Field K] [NumberField K]

private theorem exists_finset_primeFibre_canonical (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ 𝔓, 𝔓 ∈ T ↔ 𝔓 ∈ primeFibre ℚ K p) ∧ T.card ≤ Module.finrank ℚ K := by
  classical
  have hp0 : p.asIdeal ≠ ⊥ := p.ne_bot
  haveI : p.asIdeal.IsMaximal := p.isMaximal
  have hinjalg : Function.Injective (algebraMap (𝓞 ℚ) (𝓞 K)) :=
    ringHom_ringOfIntegers_rat_injective' _
  haveI : FaithfulSMul (𝓞 ℚ) (𝓞 K) := inferInstance
  haveI : NoZeroSMulDivisors (𝓞 ℚ) (𝓞 K) :=
    ⟨fun {c x} h => by
      rw [Algebra.smul_def] at h
      rcases mul_eq_zero.1 h with hc | hx
      · exact Or.inl (hinjalg (by rw [hc, map_zero]))
      · exact Or.inr hx⟩
  haveI : Module.IsTorsionFree (𝓞 ℚ) (𝓞 K) := by infer_instance
  have hmem : ∀ 𝔓 : HeightOneSpectrum (𝓞 K),
      𝔓 ∈ primeFibre ℚ K p ↔ 𝔓.asIdeal ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K) := by
    intro 𝔓
    rw [mem_primeFibre, IsDedekindDomain.mem_primesOverFinset_iff hp0]
    change _ ↔ 𝔓.asIdeal.IsPrime ∧ 𝔓.asIdeal.LiesOver p.asIdeal
    constructor
    · intro h
      refine ⟨𝔓.isPrime, ⟨?_⟩⟩
      rw [← h]
      rfl
    · rintro ⟨-, hover⟩
      apply HeightOneSpectrum.ext_iff.mpr
      exact (hover.over).symm
  have hinj : Set.InjOn (HeightOneSpectrum.asIdeal (R := 𝓞 K))
      (HeightOneSpectrum.asIdeal ⁻¹' ↑(IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K))) :=
    fun x _ y _ hxy => HeightOneSpectrum.ext_iff.mpr hxy
  refine ⟨(IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).preimage HeightOneSpectrum.asIdeal
    hinj, ?_, ?_⟩
  · intro 𝔓
    rw [Finset.mem_preimage, hmem]
  · calc ((IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).preimage
            HeightOneSpectrum.asIdeal hinj).card
        ≤ (IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)).card :=
          Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal
            (fun 𝔓 h𝔓 => Finset.mem_preimage.mp h𝔓)
            (fun x _ y _ hxy => HeightOneSpectrum.ext_iff.mpr hxy)
      _ ≤ Module.finrank ℚ K := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp0

variable [inst : Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

private theorem exists_finset_primeFibre (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ 𝔓, 𝔓 ∈ T ↔ 𝔓 ∈ primeFibre ℚ K p) ∧ T.card ≤ Module.finrank ℚ K := by
  obtain rfl : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    algebra_eq_inst_ringOfIntegersAlgebra' K inst
  exact exists_finset_primeFibre_canonical K p

omit [NumberField K] in

private theorem norm_coeff_prod_inducedFactor_le (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (hc : ∀ 𝔓, ‖c 𝔓‖ ≤ 1) (T : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) :
    ‖(∏ 𝔓 ∈ T, inducedFactor ℚ c 𝔓).coeff k‖ ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
    split_ifs <;> simp
  | @insert 𝔓 T h𝔓 ih =>
    rw [Finset.prod_insert h𝔓, Finset.card_insert_of_notMem h𝔓, mul_comm]
    have hfac : (∏ x ∈ T, inducedFactor ℚ c x) * inducedFactor ℚ c 𝔓 =
        (∏ x ∈ T, inducedFactor ℚ c x) -
          (∏ x ∈ T, inducedFactor ℚ c x) *
            X ^ ((𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) * C (c 𝔓) := by
      simp only [inducedFactor, map_one]
      ring
    rw [hfac, Polynomial.coeff_sub, Polynomial.coeff_mul_C, Polynomial.coeff_mul_X_pow']
    have h1 := ih k
    have h2 : ‖(if (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ k then
        (∏ x ∈ T, inducedFactor ℚ c x).coeff
          (k - (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) else 0)‖ ≤ 2 ^ T.card := by
      split_ifs
      · exact ih _
      · simp
    calc _ ≤ ‖(∏ x ∈ T, inducedFactor ℚ c x).coeff k‖ +
          ‖(if (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal ≤ k then
              (∏ x ∈ T, inducedFactor ℚ c x).coeff
                (k - (𝔓.under (𝓞 ℚ)).asIdeal.inertiaDeg' 𝔓.asIdeal) else 0) * c 𝔓‖ :=
          norm_sub_le _ _
      _ ≤ 2 ^ T.card + 2 ^ T.card * 1 := by
          rw [norm_mul]
          exact add_le_add h1 (mul_le_mul h2 (hc 𝔓) (norm_nonneg _) (by positivity))
      _ = 2 ^ (T.card + 1) := by ring

private theorem norm_inducedE_le (c : HeightOneSpectrum (𝓞 K) → ℂ) (hc : ∀ 𝔓, ‖c 𝔓‖ ≤ 1)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ‖inducedE1 ℚ c p‖ ≤ 2 ^ Module.finrank ℚ K ∧ ‖inducedE2 ℚ c p‖ ≤ 2 ^ Module.finrank ℚ K ∧
      ‖inducedE3 ℚ c p‖ ≤ 2 ^ Module.finrank ℚ K := by
  obtain ⟨T, hT, hcard⟩ := exists_finset_primeFibre K p
  have hset : primeFibre ℚ K p = ↑T := Set.ext fun 𝔓 => (hT 𝔓).symm
  have hprod : inducedEulerPoly ℚ c p = ∏ 𝔓 ∈ T, inducedFactor ℚ c 𝔓 := by
    rw [inducedEulerPoly, hset, finprod_mem_coe_finset]
  have hk : ∀ k, ‖(inducedEulerPoly ℚ c p).coeff k‖ ≤ 2 ^ Module.finrank ℚ K := fun k => by
    rw [hprod]
    exact (norm_coeff_prod_inducedFactor_le K c hc T k).trans
      (pow_le_pow_right₀ (by norm_num) hcard)
  refine ⟨?_, ?_, ?_⟩
  · rw [inducedE1, norm_neg]
    exact hk 1
  · rw [inducedE2]
    exact hk 2
  · rw [inducedE3, norm_neg]
    exact hk 3

end Fibre

end ConvFibre

section EulerAnalytic
open Polynomial Filter Topology

variable {ι : Type}

private theorem norm_eval_cpow_sub_one_le_majorant {q : ℕ} (hq : 1 ≤ q) (P : ℂ[X]) {n : ℕ} (hdeg : P.natDegree ≤ n)
    (h0 : P.coeff 0 = 1) {σ₁ : ℝ} {s : ℂ} (hs : σ₁ ≤ s.re) :
    ‖P.eval ((q : ℂ) ^ (-s)) - 1‖ ≤ ∑ k ∈ Finset.range n, ‖P.coeff (k + 1)‖ * (q : ℝ) ^ (-(σ₁ * (k + 1))) := by
  refine (norm_eval_sub_one_le P hdeg h0 _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_natCast_cpow_neg_pow q (Nat.lt_of_lt_of_le Nat.zero_lt_one hq) s (k + 1), Nat.cast_succ]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hq) ?_
  have hk : (0 : ℝ) ≤ (k : ℝ) + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hs hk]

private theorem differentiableOn_lFun_and_lFunDual (D : LDatum ι) (hq : ∀ i, 1 ≤ D.norm i)
    (hdeg : ∀ i, (D.euler i).natDegree ≤ D.degree ∧ (D.dual i).natDegree ≤ D.degree)
    (h0 : ∀ i, (D.euler i).coeff 0 = 1 ∧ (D.dual i).coeff 0 = 1)
    (hcoeff : ∀ s : ℂ, D.abscissa < s.re → ∀ k : ℕ, k < D.degree →
      (Summable fun i => ‖(D.euler i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(s.re * (k + 1)))) ∧
      (Summable fun i => ‖(D.dual i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(s.re * (k + 1)))))
    (hconv : D.Converges) :
    DifferentiableOn ℂ D.LFun {s : ℂ | D.abscissa < s.re} ∧
      DifferentiableOn ℂ D.LFunDual {s : ℂ | D.abscissa < s.re} := by
  have hqne : ∀ i, (D.norm i : ℂ) ≠ 0 := fun i => by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (hq i)).ne'
  have hcpow : ∀ i, Differentiable ℂ fun s : ℂ => (D.norm i : ℂ) ^ (-s) := fun i =>
    differentiable_neg.const_cpow (Or.inl (hqne i))
  constructor
  · show DifferentiableOn ℂ (fun s => ∏' i, ((D.euler i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹) _
    refine differentiableOn_tprod_inv_of_forall_exists_summable
      (fun i s => (D.euler i).eval ((D.norm i : ℂ) ^ (-s))) D.abscissa (fun i => ?_) (fun s hs i => ?_)
      (fun σ₁ hσ₁ => ?_)
    · exact (D.euler i).differentiable.comp (hcpow i)
    · exact factor_ne_zero_of_tprod_inv_ne_zero (fun j => (D.euler j).eval ((D.norm j : ℂ) ^ (-s)))
        (hconv s hs).2.2.1 i
    · refine ⟨fun i => ∑ k ∈ Finset.range D.degree, ‖(D.euler i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(σ₁ * (k + 1))),
        ?_, fun i s hs => norm_eval_cpow_sub_one_le_majorant (hq i) (D.euler i) (hdeg i).1 (h0 i).1 hs⟩
      refine summable_sum fun k hk => ?_
      have hc := (hcoeff (σ₁ : ℂ) (by simpa using hσ₁) k (Finset.mem_range.mp hk)).1
      simpa only [Complex.ofReal_re] using hc
  · show DifferentiableOn ℂ (fun s => ∏' i, ((D.dual i).eval ((D.norm i : ℂ) ^ (-s)))⁻¹) _
    refine differentiableOn_tprod_inv_of_forall_exists_summable
      (fun i s => (D.dual i).eval ((D.norm i : ℂ) ^ (-s))) D.abscissa (fun i => ?_) (fun s hs i => ?_)
      (fun σ₁ hσ₁ => ?_)
    · exact (D.dual i).differentiable.comp (hcpow i)
    · exact factor_ne_zero_of_tprod_inv_ne_zero (fun j => (D.dual j).eval ((D.norm j : ℂ) ^ (-s)))
        (hconv s hs).2.2.2 i
    · refine ⟨fun i => ∑ k ∈ Finset.range D.degree, ‖(D.dual i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(σ₁ * (k + 1))),
        ?_, fun i s hs => norm_eval_cpow_sub_one_le_majorant (hq i) (D.dual i) (hdeg i).2 (h0 i).2 hs⟩
      refine summable_sum fun k hk => ?_
      have hc := (hcoeff (σ₁ : ℂ) (by simpa using hσ₁) k (Finset.mem_range.mp hk)).2
      simpa only [Complex.ofReal_re] using hc

end EulerAnalytic

section EulerAnalyticDatum
open Polynomial IsDedekindDomain NumberField AutomorphicForm

open scoped Classical in

private theorem differentiableOn_lFun_rsDatum
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (gammaR gammaC gammaRDual gammaCDual : Multiset ℂ)
    (hμ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Pi.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Pi.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (hroot : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ γ δ : ℂ, γ + δ = Pi.a p ∧ γ * δ = Pi.b p ∧
      ‖γ‖ < Real.sqrt (Ideal.absNorm p.asIdeal) ∧ ‖δ‖ < Real.sqrt (Ideal.absNorm p.asIdeal)) :
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFun
      {s : ℂ | (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} ∧
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFunDual
      {s : ℂ | (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} := by

  have hconv := LanglandsTunnell.RankinSelberg.converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt K hdeg Pi μ
    SQ gammaR gammaC gammaRDual gammaCDual hμ hb ha hroot

  generalize hcdef : (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) = c at hconv ⊢
  have hc : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ‖c 𝔓‖ ≤ 1 := by
    intro 𝔓
    subst hcdef
    show ‖(if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)‖ ≤ 1
    by_cases h : IsUnramifiedCharAt μ 𝔓
    · rw [if_pos h, hμ 𝔓 h]
    · rw [if_neg h, norm_zero]
      exact zero_le_one
  have hc' : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), ‖(c 𝔓)⁻¹‖ ≤ 1 := by
    intro 𝔓
    subst hcdef
    show ‖(if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹‖ ≤ 1
    rw [norm_inv]
    by_cases h : IsUnramifiedCharAt μ 𝔓
    · rw [if_pos h, hμ 𝔓 h, inv_one]
    · rw [if_neg h, norm_zero, inv_zero]
      exact zero_le_one

  set E : ℝ := 2 ^ Module.finrank ℚ K
  have hE : 0 ≤ E := by positivity
  have hC : (0 : ℝ) ≤ 8 * (E + 1) ^ 3 := by positivity
  refine differentiableOn_lFun_and_lFunDual _ ?_ ?_ ?_ ?_ hconv
  ·
    intro i
    dsimp only [rsDatum]
    exact Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_ne_zero_of_nonZeroDivisors ⟨i.1.asIdeal, mem_nonZeroDivisors_of_ne_zero i.1.ne_bot⟩)
  ·
    intro i
    dsimp only [rsDatum]
    exact ⟨natDegree_rsEulerPoly_le _ _ _ _ _, natDegree_rsEulerPoly_le _ _ _ _ _⟩
  ·
    intro i
    dsimp only [rsDatum]
    exact ⟨coeff_rsEulerPoly_zero _ _ _ _ _, coeff_rsEulerPoly_zero _ _ _ _ _⟩
  ·
    intro s hs k hk
    dsimp only [rsDatum] at hs hk ⊢
    have hsum : Summable fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} =>
        (1 + ‖Pi.a i.1‖) * ((Ideal.absNorm i.1.asIdeal : ℕ) : ℝ) ^ (-s.re) :=
      summable_one_add_mul_rpow
        ((NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ hs).subtype _)
        ((ha s.re hs).subtype _)
    have hle : ∀ i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, ∀ j < 6,
        ‖(rsEulerPoly (Pi.a i.1) (Pi.b i.1) (inducedE1 ℚ c i.1) (inducedE2 ℚ c i.1)
          (inducedE3 ℚ c i.1)).coeff (j + 1)‖ ≤ 8 * (E + 1) ^ 3 * (1 + ‖Pi.a i.1‖) ^ (j + 1) := by
      intro i j hj
      obtain ⟨h₁, h₂, h₃⟩ := norm_inducedE_le K c hc i.1
      exact norm_coeff_rsEulerPoly_succ_le _ _ _ _ _ (hb i.1 i.2) h₁ h₂ h₃ hE j hj
    have hle' : ∀ i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ}, ∀ j < 6,
        ‖(rsEulerPoly (Pi.a i.1 / Pi.b i.1) (Pi.b i.1)⁻¹ (inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1)
          (inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1) (inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1)).coeff (j + 1)‖ ≤
            8 * (E + 1) ^ 3 * (1 + ‖Pi.a i.1‖) ^ (j + 1) := by
      intro i j hj
      obtain ⟨h₁, h₂, h₃⟩ := norm_inducedE_le K (fun 𝔓 => (c 𝔓)⁻¹) hc' i.1
      have hbinv : ‖(Pi.b i.1)⁻¹‖ = 1 := by rw [norm_inv, hb i.1 i.2, inv_one]
      have hadiv : ‖Pi.a i.1 / Pi.b i.1‖ = ‖Pi.a i.1‖ := by rw [norm_div, hb i.1 i.2, div_one]
      have := norm_coeff_rsEulerPoly_succ_le (Pi.a i.1 / Pi.b i.1) _ _ _ _ hbinv h₁ h₂ h₃ hE j hj
      rwa [hadiv] at this
    have h₁ := summable_norm_coeff_mul_rpow
      (q := fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} => Ideal.absNorm i.1.asIdeal)
      (P := fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} =>
        rsEulerPoly (Pi.a i.1) (Pi.b i.1) (inducedE1 ℚ c i.1) (inducedE2 ℚ c i.1) (inducedE3 ℚ c i.1))
      (a := fun i => ‖Pi.a i.1‖) (C := 8 * (E + 1) ^ 3) (σ := s.re) (n := 6)
      hC (fun i => norm_nonneg _) hle hsum k hk
    have h₂ := summable_norm_coeff_mul_rpow
      (q := fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} => Ideal.absNorm i.1.asIdeal)
      (P := fun i : {p : HeightOneSpectrum (𝓞 ℚ) // p ∉ SQ} =>
        rsEulerPoly (Pi.a i.1 / Pi.b i.1) (Pi.b i.1)⁻¹ (inducedE1 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1)
          (inducedE2 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1) (inducedE3 ℚ (fun 𝔓 => (c 𝔓)⁻¹) i.1))
      (a := fun i => ‖Pi.a i.1‖) (C := 8 * (E + 1) ^ 3) (σ := s.re) (n := 6)
      hC (fun i => norm_nonneg _) hle' hsum k hk
    exact ⟨h₁, h₂⟩

end EulerAnalyticDatum

end RankinSelbergHolomorphy

open scoped Classical in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (hdeg : Module.finrank ℚ K = 3)
    (Pi : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (gammaR gammaC gammaRDual gammaCDual : Multiset ℂ)
    (hμ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), IsUnramifiedCharAt μ 𝔓 →
      ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hb : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ‖Pi.b p‖ = 1)
    (ha : ∀ σ : ℝ, 1 < σ →
      Summable fun p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
        ‖Pi.a p‖ * (Ideal.absNorm p.asIdeal : ℝ) ^ (-σ))
    (hroot : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ → ∃ γ δ : ℂ, γ + δ = Pi.a p ∧ γ * δ = Pi.b p ∧
      ‖γ‖ < Real.sqrt (Ideal.absNorm p.asIdeal) ∧ ‖δ‖ < Real.sqrt (Ideal.absNorm p.asIdeal)) :
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFun
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} ∧
    DifferentiableOn ℂ
      (rsDatum ℚ SQ Pi.a Pi.b
        (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
        gammaR gammaC gammaRDual gammaCDual).LFunDual
      {s : ℂ |
        (rsDatum ℚ SQ Pi.a Pi.b
          (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
          gammaR gammaC gammaRDual gammaCDual).abscissa < s.re} :=
  RankinSelbergHolomorphy.differentiableOn_lFun_rsDatum K hdeg Pi μ SQ gammaR gammaC gammaRDual gammaCDual
    hμ hb ha hroot

end S_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_differentiableOn_lFun_rsDatum_of_summable_of_exists_norm_lt_sqrt (solution)

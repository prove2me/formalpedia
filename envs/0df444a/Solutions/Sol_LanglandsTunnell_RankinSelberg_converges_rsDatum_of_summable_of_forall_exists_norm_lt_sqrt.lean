-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/29df86f8-009b-56f2-9b84-a711e625a43b

import Definitions.Def_LanglandsTunnell_HonestLDatum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_induced_eq_finprod_twist_formalBaseChange
import Theorems.Thm_AutomorphicForm_satakePow_add_pow
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Theorems.Thm_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt

set_option autoImplicit false

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "LDatum"
namespace RankinSelberg
p2m_export "LanglandsTunnell.RankinSelberg" "primeFibre mem_primeFibre inducedFactor inducedEulerPoly inducedE1 inducedE2 inducedE3 rsEulerPoly rsDatum rsEulerPoly_induced_eq_finprod_twist_formalBaseChange"
namespace PinnedNiceness
p2m_open "LanglandsTunnell.RankinSelberg LanglandsTunnell"

section Piece_1

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

private theorem tprod_inv_ne_zero {f : ι → ℂ} (hne : ∀ i, f i ≠ 0) (hsum : Summable fun i => ‖f i - 1‖) :
    (∏' i, (f i)⁻¹) ≠ 0 := by
  have hlim : Tendsto (fun i => ‖f i - 1‖) cofinite (𝓝 0) := hsum.tendsto_cofinite_zero
  have hev : ∀ᶠ i in cofinite, ‖f i - 1‖ ∈ Set.Iio (1 / 2 : ℝ) :=
    hlim.eventually_mem (Iio_mem_nhds (by norm_num))
  have hg : Summable fun i => ‖(f i)⁻¹ - 1‖ := by
    refine Summable.of_norm_bounded_eventually (g := fun i => 2 * ‖f i - 1‖) (hsum.mul_left 2) ?_
    filter_upwards [hev] with i hi
    have hi' : ‖f i - 1‖ < 1 / 2 := hi
    rw [norm_norm]
    have hfi : (1 : ℝ) / 2 ≤ ‖f i‖ := by
      have h1 := norm_sub_norm_le (1 : ℂ) (f i)
      rw [norm_one, norm_sub_rev (1 : ℂ) (f i)] at h1
      linarith
    have hid : (f i)⁻¹ - 1 = (f i)⁻¹ * (1 - f i) := by
      rw [mul_sub, mul_one, inv_mul_cancel₀ (hne i)]
    rw [hid, norm_mul, norm_inv, norm_sub_rev (1 : ℂ) (f i),
      inv_mul_le_iff₀ (lt_of_lt_of_le (by norm_num) hfi)]
    nlinarith [norm_nonneg (f i - 1), hfi]
  have hprod : (∏' i, (1 + ((f i)⁻¹ - 1))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (fun i => by simpa using hne i) hg
  simpa using hprod

private theorem converges_of_summable_coeff (D : LDatum ι) (hq : ∀ i, 0 < D.norm i)
    (hdeg : ∀ i, (D.euler i).natDegree ≤ D.degree ∧ (D.dual i).natDegree ≤ D.degree)
    (h0 : ∀ i, (D.euler i).coeff 0 = 1 ∧ (D.dual i).coeff 0 = 1)
    (hcoeff : ∀ s : ℂ, D.abscissa < s.re → ∀ k : ℕ, k < D.degree →
      (Summable fun i => ‖(D.euler i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(s.re * (k + 1)))) ∧
      (Summable fun i => ‖(D.dual i).coeff (k + 1)‖ * (D.norm i : ℝ) ^ (-(s.re * (k + 1)))))
    (hne : ∀ s : ℂ, D.abscissa < s.re → ∀ i,
      (D.euler i).eval ((D.norm i : ℂ) ^ (-s)) ≠ 0 ∧ (D.dual i).eval ((D.norm i : ℂ) ^ (-s)) ≠ 0) :
    D.Converges := by
  show ∀ s : ℂ, D.abscissa < s.re → _
  intro s hs
  have hE : Summable fun i => ‖(D.euler i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖ :=
    summable_norm_eval_sub_one hq (fun i => (hdeg i).1) (fun i => (h0 i).1) s
      (fun k hk => (hcoeff s hs k hk).1)
  have hDl : Summable fun i => ‖(D.dual i).eval ((D.norm i : ℂ) ^ (-s)) - 1‖ :=
    summable_norm_eval_sub_one hq (fun i => (hdeg i).2) (fun i => (h0 i).2) s
      (fun k hk => (hcoeff s hs k hk).2)
  exact ⟨hE, hDl, tprod_inv_ne_zero (fun i => (hne s hs i).1) hE,
    tprod_inv_ne_zero (fun i => (hne s hs i).2) hDl⟩

end Piece_1

section Piece_2

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

end Piece_2

section Piece_3

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

end Piece_3

section Piece_4

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

end Piece_4

section Piece_5

open Polynomial IsDedekindDomain NumberField AutomorphicForm

private theorem quadFactor_ne_zero (m γ δ x : ℂ) (f : ℕ) (hf : f ≠ 0) (hm : ‖m‖ = 1)
    (hγ : ‖γ‖ * ‖x‖ < 1) (hδ : ‖δ‖ * ‖x‖ < 1) :
    1 - m * (γ ^ f + δ ^ f) * x ^ f + m ^ 2 * (γ * δ) ^ f * x ^ (2 * f) ≠ 0 := by
  have key : ∀ ρ : ℂ, ‖ρ‖ * ‖x‖ < 1 → 1 - m * ρ ^ f * x ^ f ≠ 0 := by
    intro ρ hρ
    have hlt : ‖m * ρ ^ f * x ^ f‖ < 1 := by
      rw [norm_mul, norm_mul, hm, one_mul, norm_pow, norm_pow, ← mul_pow]
      exact pow_lt_one₀ (by positivity) hρ hf
    have hne : m * ρ ^ f * x ^ f ≠ 1 := by
      intro h
      rw [h, norm_one] at hlt
      exact lt_irrefl _ hlt
    exact sub_ne_zero.mpr hne.symm
  have hfac : 1 - m * (γ ^ f + δ ^ f) * x ^ f + m ^ 2 * (γ * δ) ^ f * x ^ (2 * f) =
      (1 - m * γ ^ f * x ^ f) * (1 - m * δ ^ f * x ^ f) := by ring
  rw [hfac]
  exact mul_ne_zero (key γ hγ) (key δ hδ)

private theorem dual_rewrite (m γ δ : ℂ) (f : ℕ) (hγ : γ ≠ 0) (hδ : δ ≠ 0) (hm : m ≠ 0) (y : ℂ) :
    1 - m⁻¹ * ((γ ^ f + δ ^ f) / (γ * δ) ^ f) * y + (m ^ 2)⁻¹ * ((γ * δ) ^ f)⁻¹ * y ^ 2 =
      1 - m⁻¹ * (γ⁻¹ ^ f + δ⁻¹ ^ f) * y + m⁻¹ ^ 2 * (γ⁻¹ * δ⁻¹) ^ f * y ^ 2 := by
  have hγf : γ ^ f ≠ 0 := pow_ne_zero _ hγ
  have hδf : δ ^ f ≠ 0 := pow_ne_zero _ hδ
  rw [inv_pow, inv_pow, mul_pow, mul_pow, inv_pow, inv_pow, inv_pow]
  field_simp
  ring

section Dock

variable (K : Type) [Field K] [NumberField K] [inst : Algebra (𝓞 ℚ) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]

omit inst [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)] in

private theorem algebra_eq_inst_ringOfIntegersAlgebra'' (i : Algebra (𝓞 ℚ) (𝓞 K)) :
    i = NumberField.inst_ringOfIntegersAlgebra ℚ K := by
  refine Algebra.algebra_ext _ _ fun x => ?_
  have h : (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ i).comp Rat.ringOfIntegersEquiv.symm.toRingHom =
      (@algebraMap (𝓞 ℚ) (𝓞 K) _ _ (NumberField.inst_ringOfIntegersAlgebra ℚ K)).comp
        Rat.ringOfIntegersEquiv.symm.toRingHom :=
    RingHom.ext_int _ _
  have hx := RingHom.congr_fun h (Rat.ringOfIntegersEquiv x)
  rw [RingHom.comp_apply, RingHom.comp_apply] at hx
  have he : Rat.ringOfIntegersEquiv.symm.toRingHom (Rat.ringOfIntegersEquiv x) = x :=
    Rat.ringOfIntegersEquiv.symm_apply_apply x
  rwa [he] at hx

open scoped Classical in

private theorem eval_rsEulerPoly_ne_zero (hdeg : Module.finrank ℚ K = 3) (Pi : HeckeEigensystem ℚ ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (p : HeightOneSpectrum (𝓞 ℚ))
    (hμ : ∀ 𝔓 : HeightOneSpectrum (𝓞 K), TateGlobal.IsUnramifiedCharAt μ 𝔓 →
      ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1)
    (hroots : ∃ γ δ : ℂ, γ + δ = Pi.a p ∧ γ * δ = Pi.b p ∧
      ‖γ‖ < Real.sqrt (Ideal.absNorm p.asIdeal) ∧ ‖δ‖ < Real.sqrt (Ideal.absNorm p.asIdeal))
    (hb : ‖Pi.b p‖ = 1) {s : ℂ} (hs : 1 < s.re) :
    (rsEulerPoly (Pi.a p) (Pi.b p)
        (inducedE1 ℚ (fun 𝔓 => if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE2 ℚ (fun 𝔓 => if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)
        (inducedE3 ℚ (fun 𝔓 => if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) p)).eval
        ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ≠ 0 ∧
    (rsEulerPoly (Pi.a p / Pi.b p) (Pi.b p)⁻¹
        (inducedE1 ℚ (fun 𝔓 => (if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE2 ℚ (fun 𝔓 => (if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)
        (inducedE3 ℚ (fun 𝔓 => (if TateGlobal.IsUnramifiedCharAt μ 𝔓
          then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)⁻¹) p)).eval
        ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) ≠ 0 := by

  obtain rfl : inst = NumberField.inst_ringOfIntegersAlgebra ℚ K :=
    algebra_eq_inst_ringOfIntegersAlgebra'' K inst
  obtain ⟨hid, hidd⟩ := rsEulerPoly_induced_eq_finprod_twist_formalBaseChange K hdeg Pi μ p
  obtain ⟨γ, δ, hγδ, hγδ', hγ, hδ⟩ := hroots
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

  have hfin : (primeFibre ℚ K p).Finite := by
    refine (Set.Finite.preimage (f := HeightOneSpectrum.asIdeal)
      (fun x _ y _ hxy => HeightOneSpectrum.ext_iff.mpr hxy)
      (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 K))).subset ?_
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    exact ⟨𝔓.isPrime, ⟨by rw [← h𝔓]; rfl⟩⟩

  have hprod : ∀ (g : HeightOneSpectrum (𝓞 K) → ℂ[X]) (x : ℂ),
      (∀ 𝔓 ∈ primeFibre ℚ K p, (g 𝔓).eval x ≠ 0) → (∏ᶠ 𝔓 ∈ primeFibre ℚ K p, g 𝔓).eval x ≠ 0 := by
    intro g x hg
    rw [finprod_mem_eq_finite_toFinset_prod g hfin, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro 𝔓 h𝔓
    exact hg 𝔓 (hfin.mem_toFinset.mp h𝔓)

  set q : ℕ := Ideal.absNorm p.asIdeal with hq_def
  have hq0 : q ≠ 0 := by
    rw [hq_def, Ne, Ideal.absNorm_eq_zero_iff]
    exact p.ne_bot
  have hq1 : q ≠ 1 := by
    rw [hq_def, Ne, Ideal.absNorm_eq_one_iff]
    exact p.isPrime.ne_top
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hqpos : (0 : ℝ) < q := by linarith
  set x : ℂ := (q : ℂ) ^ (-s) with hx_def
  have hxnorm : ‖x‖ ≤ (q : ℝ)⁻¹ := by
    rw [hx_def, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hsqrt : Real.sqrt q * (q : ℝ)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hqpos, one_mul]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hsmall : ∀ ρ : ℂ, ‖ρ‖ < Real.sqrt q → ‖ρ‖ * ‖x‖ < 1 := by
    intro ρ hρ
    calc ‖ρ‖ * ‖x‖ ≤ ‖ρ‖ * (q : ℝ)⁻¹ := by gcongr
      _ < Real.sqrt q * (q : ℝ)⁻¹ := by gcongr
      _ ≤ 1 := hsqrt
  have hγx : ‖γ‖ * ‖x‖ < 1 := hsmall γ hγ
  have hδx : ‖δ‖ * ‖x‖ < 1 := hsmall δ hδ

  have hbne : Pi.b p ≠ 0 := by
    intro h; rw [h, norm_zero] at hb; exact zero_ne_one hb
  have hγ0 : γ ≠ 0 := by
    intro h; apply hbne; rw [← hγδ', h, zero_mul]
  have hδ0 : δ ≠ 0 := by
    intro h; apply hbne; rw [← hγδ', h, mul_zero]
  have hnormγδ : ‖γ‖ * ‖δ‖ = 1 := by rw [← norm_mul, hγδ', hb]
  have hγinv : ‖γ⁻¹‖ * ‖x‖ < 1 := by
    have : ‖γ⁻¹‖ = ‖δ‖ := by
      rw [norm_inv]
      field_simp
      linarith [hnormγδ]
    rw [this]; exact hδx
  have hδinv : ‖δ⁻¹‖ * ‖x‖ < 1 := by
    have : ‖δ⁻¹‖ = ‖γ‖ := by
      rw [norm_inv]
      field_simp
      linarith [hnormγδ]
    rw [this]; exact hγx

  have hfne : ∀ 𝔓 ∈ primeFibre ℚ K p, p.asIdeal.inertiaDeg' 𝔓.asIdeal ≠ 0 := by
    intro 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    haveI : 𝔓.asIdeal.LiesOver p.asIdeal := ⟨by rw [← h𝔓]; rfl⟩
    exact Ideal.inertiaDeg_ne_zero p.asIdeal 𝔓.asIdeal
  refine ⟨?_, ?_⟩
  · rw [hid]
    refine hprod _ x fun 𝔓 h𝔓 => ?_
    have hf := hfne 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    by_cases hun : TateGlobal.IsUnramifiedCharAt μ 𝔓
    · have hm : ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1 := hμ 𝔓 hun
      have hq := quadFactor_ne_zero ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) γ δ x
        (p.asIdeal.inertiaDeg' 𝔓.asIdeal) hf hm hγx hδx
      rw [if_pos hun]
      simp only [formalBaseChange, h𝔓, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        Units.val_pow_eq_pow_val]
      intro h0
      apply hq
      rw [← hγδ, ← hγδ', satakePow_add_pow γ δ] at h0
      linear_combination h0
    · rw [if_neg hun, eval_C]
      exact one_ne_zero
  · rw [hidd]
    refine hprod _ x fun 𝔓 h𝔓 => ?_
    have hf := hfne 𝔓 h𝔓
    rw [mem_primeFibre] at h𝔓
    by_cases hun : TateGlobal.IsUnramifiedCharAt μ 𝔓
    · have hm : ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)‖ = 1 := hμ 𝔓 hun
      have hm0 : ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have hm' : ‖((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)⁻¹‖ = 1 := by rw [norm_inv, hm, inv_one]
      have hq := quadFactor_ne_zero ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ)⁻¹ γ⁻¹ δ⁻¹ x
        (p.asIdeal.inertiaDeg' 𝔓.asIdeal) hf hm' hγinv hδinv
      have hdual := dual_rewrite ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) γ δ
        (p.asIdeal.inertiaDeg' 𝔓.asIdeal) hγ0 hδ0 hm0 (x ^ p.asIdeal.inertiaDeg' 𝔓.asIdeal)
      rw [if_pos hun]
      simp only [formalBaseChange, h𝔓, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
        Units.val_inv_eq_inv_val, Units.val_mul, zpow_neg, zpow_two]
      intro h0
      apply hq
      rw [← hγδ, ← hγδ', satakePow_add_pow γ δ] at h0
      simp only [div_eq_mul_inv, inv_pow, mul_pow, mul_inv] at h0 hdual ⊢
      linear_combination h0 - hdual
    · rw [if_neg hun, eval_C]
      exact one_ne_zero

end Dock

end Piece_5

end LanglandsTunnell.RankinSelberg.PinnedNiceness

open LanglandsTunnell.RankinSelberg.PinnedNiceness in
open _root_.LanglandsTunnell.RankinSelberg _root_.P2MW.S_LanglandsTunnell_RankinSelberg_converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt.LanglandsTunnell.RankinSelberg IsDedekindDomain NumberField AutomorphicForm NumberField.TateGlobal in
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
    (rsDatum ℚ SQ Pi.a Pi.b
      (fun 𝔓 => if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0)
      gammaR gammaC gammaRDual gammaCDual).Converges := by

  generalize hcdef : (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
    if IsUnramifiedCharAt μ 𝔓 then ((μ (uniformizerIdele K 𝔓) : ℂˣ) : ℂ) else 0) = c
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
  refine converges_of_summable_coeff _ ?_ ?_ ?_ ?_ ?_
  ·
    intro i
    dsimp only [rsDatum]
    exact Nat.pos_of_ne_zero
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
  ·
    intro s hs i
    dsimp only [rsDatum] at hs ⊢
    subst hcdef
    exact eval_rsEulerPoly_ne_zero K hdeg Pi μ i.1 hμ (hroot i.1 i.2) (hb i.1 i.2) hs

end

end S_LanglandsTunnell_RankinSelberg_converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_converges_rsDatum_of_summable_of_forall_exists_norm_lt_sqrt (solution)

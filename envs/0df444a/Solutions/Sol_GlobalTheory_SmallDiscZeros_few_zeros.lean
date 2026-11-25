-- Prove2me | solution 1 for GlobalTheory.SmallDiscZeros.few_zeros
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:07.059128+00:00
-- url     : https://prove2.me/submissions/7c896325-3677-41c1-9572-314816c145a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
import Theorems.Thm_GlobalTheory_LogDerivHigher_main
import Theorems.Thm_GlobalTheory_LogDerivZeros_main

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
namespace GlobalTheory.SmallDiscZeros
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma derSeries_one_eq_tsum_vonMangoldt (σ : ℝ) :
    _root_.GlobalTheory.Lin.derSeries (fun n ↦ (1 : DirichletCharacter ℂ 1) n) 0 ((σ : ℂ) + (0 : ℝ) * I) =
      ((∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  dsimp only
  rw [MulChar.one_apply (isUnit_of_subsingleton _)]
  push_cast
  rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
  simp
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma re_natCast_div_pow_zero_add_one (m : ℕ) (z : ℂ) :
    ((m : ℂ) / z ^ (0 + 1)).re = m * (z⁻¹).re := by
  rw [zero_add, pow_one, div_eq_mul_inv, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma re_lt_one_of_mem_zerosDisc {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {c w : ℂ}
    {R : ℝ} (hw : w ∈ _root_.GlobalTheory.Lin.zerosDisc χ c R) : w.re < 1 := by
  simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw
  obtain ⟨-, h1, h0⟩ := hw
  by_contra h
  exact LFunction_ne_zero_of_one_le_re χ h1 (not_lt.mp h) h0
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma inv_re_nonneg_of_re_nonneg {z : ℂ} (h : 0 ≤ z.re) : 0 ≤ (z⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg h (Complex.normSq_nonneg _)
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma summable_vonMangoldt_mul_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ ↦ vonMangoldt n * (n : ℝ) ^ (-σ) := by
  have h := LSeriesSummable_vonMangoldt (s := (σ : ℂ)) (by simpa using hσ)
  have h' : Summable fun n ↦ ‖LSeries.term (fun n ↦ (vonMangoldt n : ℂ)) (σ : ℂ) n‖ :=
    summable_norm_iff.mpr h
  refine h'.congr fun n ↦ ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma norm_derSeries_le_tsum_vonMangoldt {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    ‖_root_.GlobalTheory.Lin.derSeries (fun n ↦ χ n) 0 s‖ ≤
      ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s.re) := by
  unfold _root_.GlobalTheory.Lin.derSeries
  refine tsum_of_norm_bounded (summable_vonMangoldt_mul_rpow_neg hs).hasSum fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
      Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one χ _))
      (by positivity)
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology in
open scoped Classical in
private lemma inv_re_ge_of_norm_sub_le {t r : ℝ} {w : ℂ} (hr : 0 < r) (hw : ‖w - (1 + t * I)‖ ≤ r)
    (hre : w.re < 1) : 1 / (4 * r) ≤ ((((1 + r : ℝ) : ℂ) + t * I - w)⁻¹).re := by
  set z : ℂ := ((1 + r : ℝ) : ℂ) + t * I - w with hz
  have hzre : z.re = 1 + r - w.re := by simp [hz]
  have hzre' : r < z.re := by linarith
  have hznorm : ‖z‖ ≤ 2 * r := by
    have hz' : z = (r : ℂ) - (w - (1 + t * I)) := by rw [hz]; push_cast; ring
    rw [hz']
    calc ‖(r : ℂ) - (w - (1 + t * I))‖ ≤ ‖(r : ℂ)‖ + ‖w - (1 + t * I)‖ := norm_sub_le _ _
      _ ≤ r + r := by rw [Complex.norm_real, Real.norm_of_nonneg hr.le]; linarith
      _ = 2 * r := by ring
  have hpos : 0 < Complex.normSq z := by
    refine Complex.normSq_pos.mpr fun h ↦ ?_
    rw [h, Complex.zero_re] at hzre'
    linarith
  rw [Complex.inv_re, div_le_div_iff₀ (by positivity) hpos, Complex.normSq_eq_norm_sq]
  nlinarith [mul_le_mul hznorm hznorm (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * r)]
end GlobalTheory.SmallDiscZeros
end

set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.SmallDiscZeros
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical
namespace GlobalTheory.SmallDiscZeros
namespace _root_.GlobalTheory.SmallDiscZeros
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (_root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  obtain ⟨C, hC, hmain⟩ := _root_.GlobalTheory.LogDerivHigher.main
  refine ⟨6 + 4 * C, by positivity, ?_⟩
  intro q _ χ t r hχt hr hr2
  have hσ1 : 1 < 1 + r := by linarith
  have hσ2 : 1 + r ≤ 2 := by linarith
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hL0 : 0 ≤ Real.log (q * (|t| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg t])
  have hTS : _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r ⊆ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3 := by
    intro w hw
    simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw ⊢
    refine ⟨?_, hw.2⟩
    calc ‖w - (2 + t * I)‖ = ‖(w - (1 + t * I)) - 1‖ := by ring_nf
      _ ≤ ‖w - (1 + t * I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith [hw.1]
  obtain ⟨hfin, -, hbound⟩ := hmain q χ (1 + r) t 0 hσ1 hσ2
  obtain ⟨hfin₁, -, hbound₁⟩ := hmain 1 1 (1 + r) 0 0 hσ1 hσ2
  have hTfin := hfin.subset hTS
  refine ⟨hTfin, ?_⟩
  set G : ℝ := ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + r)) with hG
  have hG_le : G ≤ 1 / r + C := by
    rw [derSeries_one_eq_tsum_vonMangoldt, if_pos rfl] at hbound₁
    have hP : (1 : ℂ) / (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - 1) ^ (0 + 1) = ((1 / r : ℝ) : ℂ) := by
      push_cast; ring
    rw [hP] at hbound₁
    have hZ₁ : 0 ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc (1 : DirichletCharacter ℂ 1) (2 + (0 : ℝ) * I) 3,
        ((_root_.GlobalTheory.Lin.ord (1 : DirichletCharacter ℂ 1) w : ℕ) : ℂ) /
          (((1 + r : ℝ) : ℂ) + (0 : ℝ) * I - w) ^ (0 + 1)).re := by
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin₁, Complex.re_sum]
      refine Finset.sum_nonneg fun w hw ↦ ?_
      rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin₁).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
    have hre := (Complex.re_le_norm _).trans hbound₁
    rw [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    have hlog : Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) ≤ 1 := by
      norm_num
      linarith [Real.log_two_lt_d9]
    have hCl : C * Real.log ((1 : ℕ) * (|(0 : ℝ)| + 2)) / (1 + r) ^ 0 ≤ C := by
      rw [pow_zero, div_one]
      nlinarith
    linarith
  have key : ∀ (X Y W : ℂ) (B : ℝ), ‖(X - Y) + W‖ ≤ B → ‖W‖ ≤ B + ‖X‖ + ‖Y‖ := by
    intro X Y W B h
    have hW : W = ((X - Y) + W) - X + Y := by ring
    rw [hW]
    calc ‖((X - Y) + W) - X + Y‖ ≤ ‖(X - Y) + W‖ + ‖X‖ + ‖Y‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ B + ‖X‖ + ‖Y‖ := by linarith
  have hZnorm := key _ _ _ _ hbound
  rw [pow_zero, div_one] at hZnorm
  have hre : (((1 + r : ℝ) : ℂ) + t * I).re = 1 + r := by simp
  have hA := norm_derSeries_le_tsum_vonMangoldt χ (s := ((1 + r : ℝ) : ℂ) + t * I) (by rw [hre]; exact hσ1)
  rw [hre] at hA
  have hZn : ‖∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)‖ ≤
      C * Real.log (q * (|t| + 2)) + G + 1 := by
    split_ifs at hZnorm with h1
    · have ht : 2 ≤ |t| := hχt.resolve_left (not_not.mpr h1)
      have him : |t| ≤ ‖((1 + r : ℝ) : ℂ) + t * I - 1‖ := by
        have := Complex.abs_im_le_norm (((1 + r : ℝ) : ℂ) + t * I - 1)
        simpa using this
      have hY : ‖(1 : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - 1) ^ (0 + 1)‖ ≤ 1 := by
        rw [zero_add, pow_one, norm_div, norm_one, div_le_one (by linarith)]
        linarith
      linarith
    · rw [norm_zero] at hZnorm
      linarith
  have hZre : (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) *
      (1 / (4 * r)) ≤ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (2 + t * I) 3,
      ((_root_.GlobalTheory.Lin.ord χ w : ℕ) : ℂ) / (((1 + r : ℝ) : ℂ) + t * I - w) ^ (0 + 1)).re := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hTfin, Finset.sum_mul,
      finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    refine (Finset.sum_le_sum fun w hw ↦ ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Set.Finite.toFinset_subset_toFinset.mpr hTS)
        fun w hw _ ↦ ?_)
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := (Set.Finite.mem_toFinset hTfin).mp hw
      refine mul_le_mul_of_nonneg_left (inv_re_ge_of_norm_sub_le hr ?_ (re_lt_one_of_mem_zerosDisc hw'))
        (Nat.cast_nonneg _)
      simp only [_root_.GlobalTheory.Lin.zerosDisc, Set.mem_setOf_eq] at hw'
      exact hw'.1
    · rw [re_natCast_div_pow_zero_add_one]
      have hw' := re_lt_one_of_mem_zerosDisc ((Set.Finite.mem_toFinset hfin).mp hw)
      refine mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_of_re_nonneg ?_)
      simp
      linarith
  set N := ∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ) with hN
  set L := Real.log (q * (|t| + 2)) with hL
  have h1 : N * (1 / (4 * r)) ≤ C * L + G + 1 := hZre.trans ((Complex.re_le_norm _).trans hZn)
  have h2 : N ≤ 4 * r * (C * L + G + 1) := by
    have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 4 * r)
    have e : 4 * r * (N * (1 / (4 * r))) = N := by field_simp
    linarith
  have h3 : 4 * r * (C * L + G + 1) ≤ 4 * (C * (r * L)) + 4 + 4 * r * (C + 1) := by
    have e : 4 * r * (1 / r) = 4 := by field_simp
    have h5 := mul_le_mul_of_nonneg_left hG_le (by positivity : (0 : ℝ) ≤ 4 * r)
    nlinarith
  have hrL : 0 ≤ r * L := by positivity
  have h6 := mul_le_mul_of_nonneg_right hr2 (by positivity : (0 : ℝ) ≤ C + 1)
  nlinarith [mul_nonneg hC.le hrL]
end _root_.GlobalTheory.SmallDiscZeros
end GlobalTheory.SmallDiscZeros

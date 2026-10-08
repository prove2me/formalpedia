-- Prove2me | solution 1 for OAI.InternalCatalan.barrier_case2_norm_rational_upper
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T19:02:23.760717+00:00
-- url     : https://prove2.me/submissions/fa0ea200-b3e7-4e23-954d-7b31c644525e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_OAICatalanIrrationality

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTailPairRational
namespace OAI

noncomputable section

namespace InternalCatalan













theorem barrier_finite_lengths :
    barrierP2Finite.length = 10 ∧ barrierV2Finite.length = 10 ∧
    barrierP1Finite.length = 8 ∧ barrierV1Finite.length = 8 := by decide

theorem barrier_tail_lengths : barrierP2Tail.length = 10 ∧ barrierV2Tail.length = 13 := by
  norm_num [barrierP2Tail, barrierV2Tail, barrierConjugatePair]


theorem barrierP2_finite_abs_lt_one :
    ∀ a ∈ barrierP2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP2Finite]

theorem barrierV2_finite_abs_lt_one :
    ∀ a ∈ barrierV2Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV2Finite]

theorem barrierP1_finite_abs_lt_one :
    ∀ a ∈ barrierP1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierP1Finite]

theorem barrierV1_finite_abs_lt_one :
    ∀ a ∈ barrierV1Finite, |(a : ℝ) / 100000000| < 1 := by
  norm_num [barrierV1Finite]

theorem barrierP2_tail_norm_bounds :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (94 / 100 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierP2Tail,
      Complex.normSq zr.1 ≤ (94 / 100 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierP2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierV2_tail_norm_bounds :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (984 / 1000 : ℝ) ∧ ‖zr.2‖ < 1 := by
  have hs : ∀ zr ∈ barrierV2Tail,
      Complex.normSq zr.1 ≤ (984 / 1000 : ℝ) ^ 2 ∧ Complex.normSq zr.2 < 1 := by
    norm_num [barrierV2Tail, barrierConjugatePair, barrierComplex,
      Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]
  intro zr hzr
  obtain ⟨hb, hr⟩ := hs zr hzr
  rw [Complex.normSq_eq_norm_sq] at hb hr
  constructor
  · nlinarith only [hb, norm_nonneg zr.1]
  · nlinarith only [hr, norm_nonneg zr.2]

theorem barrierFiniteCoeff_abs_le (cs : List ℤ) (hlen : cs.length ≤ 10)
    (hcoeff : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1) (k : ℕ) :
    |barrierFiniteCoeff cs k| ≤ 2 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · subst k
    norm_num [barrierFiniteCoeff]
  rw [barrierFiniteCoeff, if_neg hk]
  by_cases hi : k - 1 < cs.length
  · have hmem : cs.getD (k - 1) 0 ∈ cs := by
      rw [List.getD_eq_getElem cs 0 hi]
      exact List.getElem_mem hi
    have hk10 : k ≤ 10 := by omega
    have hpow : (99 / 100 : ℝ) ^ 10 ≤ (99 / 100 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk10
    calc
      |(cs.getD (k - 1) 0 : ℝ) / 100000000| ≤ 1 :=
        le_of_lt (hcoeff _ hmem)
      _ ≤ 2 * (99 / 100 : ℝ) ^ 10 := by norm_num
      _ ≤ 2 * (99 / 100 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hpow (by norm_num)
  · rw [List.getD_eq_default cs 0 (Nat.le_of_not_gt hi)]
    simp only [Int.cast_zero, zero_div, abs_zero]
    exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _)


def barrierTailQuadraticDen (z : ℂ) (x : ℝ) : ℂ :=
  1 - 2 * (x : ℂ) * z + z ^ 2











theorem barrierComplex_real_pow (a : ℚ) (k : ℕ) :
    (barrierComplex a 0) ^ k = (((a : ℝ) ^ k : ℝ) : ℂ) := by
  have h : barrierComplex a 0 = ((a : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [barrierComplex]
  rw [h, Complex.ofReal_pow]

theorem barrierComplex_imaginary_pow (b : ℚ) (k : ℕ) :
    (barrierComplex 0 b) ^ k = (((b : ℝ) ^ k : ℝ) : ℂ) * Complex.I ^ k := by
  have h : barrierComplex 0 b = ((b : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [barrierComplex]
  rw [h, mul_pow, Complex.ofReal_pow]

theorem barrierConjugatePair_power_re (z r : ℂ) (k : ℕ) :
    ((barrierConjugatePair z r).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * (r * z ^ k).re := by
  have h : star r * star z ^ k = star (r * z ^ k) := by simp
  simp only [barrierConjugatePair, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [h]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

def barrierAxisPhase (c d : ℝ) (k : ℕ) : ℝ :=
  c * (Complex.I ^ k).re - d * (Complex.I ^ k).im

/-- Port note (prove2.me): newer Mathlib's `norm_num` evaluates `(Complex.I ^ k).re` for a numeral
`k`; Mathlib 0df444a does not, so the evaluation is supplied as a lemma. -/
theorem barrierI_pow_re_port (k : ℕ) :
    (Complex.I ^ k).re = if k % 4 = 0 then 1 else if k % 4 = 2 then -1 else 0 := by
  rw [Complex.I_pow_eq_pow_mod]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h <;>
    simp [h, pow_succ]

theorem barrierI_pow_im_port (k : ℕ) :
    (Complex.I ^ k).im = if k % 4 = 1 then 1 else if k % 4 = 3 then -1 else 0 := by
  rw [Complex.I_pow_eq_pow_mod]
  rcases (by omega : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3) with h | h | h | h <;>
    simp [h, pow_succ]

theorem barrierConjugatePair_imaginary_power_re (b c d : ℚ) (k : ℕ) :
    ((barrierConjugatePair (barrierComplex 0 b) (barrierComplex c d)).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * barrierAxisPhase (c : ℝ) (d : ℝ) k * (b : ℝ) ^ k := by
  rw [barrierConjugatePair_power_re, barrierComplex_imaginary_pow]
  simp only [barrierAxisPhase, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    barrierComplex]
  ring

def barrierV2CoefficientFormula (k : ℕ) : ℝ :=
  barrierFiniteCoeff barrierV2Finite k +
  (15199211 / 100000000) * (-8 / 10) ^ k +
  (4451662 / 100000000) * (-96 / 100) ^ k +
  (2545398 / 100000000) * (88 / 100) ^ k +
  (-4932634 / 100000000) * (95 / 100) ^ k +
  (11618157 / 100000000) * (984 / 1000) ^ k +
  2 * barrierAxisPhase (27238714 / 200000000) (38447936 / 200000000) k * (78 / 100) ^ k +
  2 * barrierAxisPhase (-31341084 / 200000000) (30188786 / 200000000) k * (9 / 10) ^ k +
  2 * barrierAxisPhase (-6693542 / 200000000) (-11912254 / 200000000) k * (955 / 1000) ^ k +
  2 * barrierAxisPhase (2055213 / 200000000) (21715849 / 200000000) k * (984 / 1000) ^ k

theorem barrierV2_eq_coefficientFormula (k : ℕ) (hk : k ≠ 0) :
    barrierV2 k = barrierV2CoefficientFormula k := by
  simp only [barrierV2, barrierTrial, if_neg hk, barrierV2Tail,
    List.map_append, List.sum_append, Complex.add_re]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  simp only [barrierConjugatePair_imaginary_power_re, barrierComplex_real_pow]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, barrierComplex]
  norm_num [barrierV2CoefficientFormula]
  ring

def barrierP2NormRows : List (ℝ × ℝ) :=
  [(85/100, 9338452/100000000), (94/100, 2141509/100000000),
   (7/10, 98185491/200000000), (7/10, 98185491/200000000),
   (85/100, 7234296/200000000), (85/100, 7234296/200000000),
   (93/100, 12154152/200000000), (93/100, 12154152/200000000),
   (93/100, 11196823/200000000), (93/100, 11196823/200000000)]

def barrierV2NormRows : List (ℝ × ℝ) :=
  [(8/10, 15199211/100000000), (96/100, 4451662/100000000),
   (88/100, 2545398/100000000), (95/100, 4932634/100000000),
   (984/1000, 11618157/100000000),
   (78/100, 65686650/200000000), (78/100, 65686650/200000000),
   (9/10, 61529870/200000000), (9/10, 61529870/200000000),
   (955/1000, 18605796/200000000), (955/1000, 18605796/200000000),
   (984/1000, 23771062/200000000), (984/1000, 23771062/200000000)]

def barrierNormMajorant (rows : List (ℝ × ℝ)) (k : ℕ) : ℝ :=
  (rows.map (fun br => br.2 * br.1 ^ k)).sum

private theorem norm_le_of_normSq_le {z : ℂ} {a : ℝ}
    (ha : 0 ≤ a) (hz : Complex.normSq z ≤ a ^ 2) : ‖z‖ ≤ a := by
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]

private theorem normRows_of_sq {tail : List (ℂ × ℂ)} {rows : List (ℝ × ℝ)}
    (h : List.Forall₂ (fun zr br => 0 ≤ br.1 ∧ 0 ≤ br.2 ∧
      Complex.normSq zr.1 ≤ br.1 ^ 2 ∧ Complex.normSq zr.2 ≤ br.2 ^ 2) tail rows) :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows := by
  exact h.imp (fun zr br hb =>
    ⟨norm_le_of_normSq_le hb.1 hb.2.2.1,
      norm_le_of_normSq_le hb.2.1 hb.2.2.2⟩)

theorem barrierP2_normRows :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2)
      barrierP2Tail barrierP2NormRows := by
  apply normRows_of_sq
  norm_num [barrierP2Tail, barrierP2NormRows, barrierConjugatePair,
    barrierComplex, Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]

theorem barrierV2_normRows :
    List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2)
      barrierV2Tail barrierV2NormRows := by
  apply normRows_of_sq
  norm_num [barrierV2Tail, barrierV2NormRows, barrierConjugatePair,
    barrierComplex, Complex.star_def, Complex.normSq_conj, Complex.normSq_mk]

theorem barrier_tail_norm_majorant {tail : List (ℂ × ℂ)} {rows : List (ℝ × ℝ)}
    (h : List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows)
    (k : ℕ) :
    ‖(tail.map (fun zr => zr.2 * zr.1 ^ k)).sum‖ ≤ barrierNormMajorant rows k := by
  induction h with
  | nil => simp [barrierNormMajorant]
  | @cons zr br tail rows hb hrest ih =>
    have hbr0 : 0 ≤ br.1 := (norm_nonneg zr.1).trans hb.1
    have hbw0 : 0 ≤ br.2 := (norm_nonneg zr.2).trans hb.2
    have hterm : ‖zr.2 * zr.1 ^ k‖ ≤ br.2 * br.1 ^ k := by
      rw [norm_mul, norm_pow]
      gcongr
      · exact hb.2
      · exact hb.1
    simpa only [List.map_cons, List.sum_cons, barrierNormMajorant] using
      (norm_add_le (zr.2 * zr.1 ^ k)
        ((tail.map (fun zr => zr.2 * zr.1 ^ k)).sum)).trans (add_le_add hterm ih)

theorem barrier_normMajorant_shift (rows : List (ℝ × ℝ)) (r : ℝ)
    (hb : ∀ br ∈ rows, 0 ≤ br.1 ∧ br.1 ≤ r ∧ 0 ≤ br.2) (K j : ℕ) :
    barrierNormMajorant rows (K + j) ≤ barrierNormMajorant rows K * r ^ j := by
  induction rows with
  | nil => simp [barrierNormMajorant]
  | cons br rows ih =>
    have hbr := hb br List.mem_cons_self
    have hbr0 : 0 ≤ br.1 := hbr.1
    have hbw0 : 0 ≤ br.2 := hbr.2.2
    have hi := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hp : br.2 * br.1 ^ (K + j) ≤ (br.2 * br.1 ^ K) * r ^ j := by
      rw [pow_add]
      calc
        _ = (br.2 * br.1 ^ K) * br.1 ^ j := by ring
        _ ≤ _ := by gcongr; exact hbr.2.1
    simpa only [barrierNormMajorant, List.map_cons, List.sum_cons, add_mul] using
      add_le_add hp hi

theorem barrierTrial_abs_le_majorant (cs : List ℤ) (tail : List (ℂ × ℂ))
    (rows : List (ℝ × ℝ))
    (hb : List.Forall₂ (fun zr br => ‖zr.1‖ ≤ br.1 ∧ ‖zr.2‖ ≤ br.2) tail rows)
    (k : ℕ) (hk : cs.length < k) :
    |barrierTrial cs tail k| ≤ barrierNormMajorant rows k := by
  have hk0 : k ≠ 0 := by omega
  have hlen : cs.length ≤ k - 1 := by omega
  simp only [barrierTrial, if_neg hk0, barrierFiniteCoeff,
    List.getD_eq_default cs 0 hlen, Int.cast_zero, zero_div, zero_add]
  exact (Complex.abs_re_le_norm _).trans (barrier_tail_norm_majorant hb k)

theorem barrierP2_tail_decay (j : ℕ) :
    |barrierP2 (j + 60 + 1)| ≤ (33 / 10000 : ℝ) * (94 / 100 : ℝ) ^ j := by
  have hstart : barrierNormMajorant barrierP2NormRows 61 ≤ (33 / 10000 : ℝ) := by
    norm_num [barrierNormMajorant, barrierP2NormRows]
  have hr : ∀ br ∈ barrierP2NormRows, 0 ≤ br.1 ∧ br.1 ≤ (94 / 100 : ℝ) ∧ 0 ≤ br.2 := by
    norm_num [barrierP2NormRows]
  calc
    _ ≤ barrierNormMajorant barrierP2NormRows (j + 60 + 1) :=
      barrierTrial_abs_le_majorant _ _ _ barrierP2_normRows _ (by
        rw [barrier_finite_lengths.1]; omega)
    _ = barrierNormMajorant barrierP2NormRows (61 + j) := by congr 1; omega
    _ ≤ barrierNormMajorant barrierP2NormRows 61 * (94 / 100 : ℝ) ^ j :=
      barrier_normMajorant_shift _ _ hr 61 j
    _ ≤ _ := mul_le_mul_of_nonneg_right hstart (by positivity)

theorem barrierV2_tail_decay (j : ℕ) :
    |barrierV2 (j + 225 + 1)| ≤ (93 / 10000 : ℝ) * (984 / 1000 : ℝ) ^ j := by
  have hstart : barrierNormMajorant barrierV2NormRows 226 ≤ (93 / 10000 : ℝ) := by
    norm_num [barrierNormMajorant, barrierV2NormRows]
  have hr : ∀ br ∈ barrierV2NormRows, 0 ≤ br.1 ∧ br.1 ≤ (984 / 1000 : ℝ) ∧ 0 ≤ br.2 := by
    norm_num [barrierV2NormRows]
  calc
    _ ≤ barrierNormMajorant barrierV2NormRows (j + 225 + 1) :=
      barrierTrial_abs_le_majorant _ _ _ barrierV2_normRows _ (by
        rw [barrier_finite_lengths.2.1]; omega)
    _ = barrierNormMajorant barrierV2NormRows (226 + j) := by congr 1; omega
    _ ≤ barrierNormMajorant barrierV2NormRows 226 * (984 / 1000 : ℝ) ^ j :=
      barrier_normMajorant_shift _ _ hr 226 j
    _ ≤ _ := mul_le_mul_of_nonneg_right hstart (by positivity)

open Polynomial
















end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFinitePotentialRat
namespace OAI

noncomputable section

namespace InternalCatalan

section

private theorem barrierTail_norm_le (tail : List (ℂ × ℂ)) (k : ℕ) :
    (∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) →
      ‖(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum‖ ≤
        (tail.length : ℝ) * (99 / 100 : ℝ) ^ k := by
  induction tail with
  | nil => simp
  | cons zr tail ih =>
    intro hb
    have hz := hb zr (List.mem_cons_self)
    have ht := ih (fun w hw => hb w (List.mem_cons_of_mem _ hw))
    have hone : ‖zr.2 * zr.1 ^ k‖ ≤ (99 / 100 : ℝ) ^ k := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ 1 * (99 / 100 : ℝ) ^ k := by
          gcongr
          · exact hz.2
          · exact hz.1
        _ = _ := one_mul _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ ‖zr.2 * zr.1 ^ k‖ + ‖(tail.map (fun w : ℂ × ℂ => w.2 * w.1 ^ k)).sum‖ :=
        norm_add_le _ _
      _ ≤ (99 / 100 : ℝ) ^ k + (tail.length : ℝ) * (99 / 100 : ℝ) ^ k :=
        add_le_add hone ht
      _ = _ := by ring

private theorem barrierTrial_abs_le (cs : List ℤ) (tail : List (ℂ × ℂ))
    (hc : cs.length ≤ 10)
    (ha : ∀ a ∈ cs, |(a : ℝ) / 100000000| < 1)
    (ht : tail.length ≤ 13)
    (hb : ∀ zr ∈ tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1) (k : ℕ) :
    |barrierTrial cs tail k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  by_cases hk : k = 0
  · simp [barrierTrial, hk]
  have htail : |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| ≤
      13 * (99 / 100 : ℝ) ^ k := by
    exact (Complex.abs_re_le_norm _).trans ((barrierTail_norm_le tail k hb).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast ht) (by positivity)))
  simp only [barrierTrial, if_neg hk]
  calc
    _ ≤ |barrierFiniteCoeff cs k| +
        |(tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (barrierFiniteCoeff cs k)
        ((tail.map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re)
    _ ≤ 2 * (99 / 100 : ℝ) ^ k + 13 * (99 / 100 : ℝ) ^ k :=
      add_le_add (barrierFiniteCoeff_abs_le cs hc ha k) htail
    _ = _ := by ring

theorem barrier_trials_abs_le (k : ℕ) :
    |barrierP2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV2 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierP1 k| ≤ 15 * (99 / 100 : ℝ) ^ k ∧
    |barrierV1 k| ≤ 15 * (99 / 100 : ℝ) ^ k := by
  have hp : ∀ zr ∈ barrierP2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierP2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  have hv : ∀ zr ∈ barrierV2Tail, ‖zr.1‖ ≤ (99 / 100 : ℝ) ∧ ‖zr.2‖ ≤ 1 := by
    intro zr hz
    have h := barrierV2_tail_norm_bounds zr hz
    exact ⟨h.1.trans (by norm_num), h.2.le⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact barrierTrial_abs_le barrierP2Finite barrierP2Tail
      barrier_finite_lengths.1.le barrierP2_finite_abs_lt_one
      (barrier_tail_lengths.1.le.trans (by norm_num)) hp k
  · exact barrierTrial_abs_le barrierV2Finite barrierV2Tail
      barrier_finite_lengths.2.1.le barrierV2_finite_abs_lt_one
      barrier_tail_lengths.2.le hv k
  · exact barrierTrial_abs_le barrierP1Finite []
      (barrier_finite_lengths.2.2.1.le.trans (by norm_num)) barrierP1_finite_abs_lt_one
      (by simp) (by simp) k
  · exact barrierTrial_abs_le barrierV1Finite []
      (barrier_finite_lengths.2.2.2.le.trans (by norm_num)) barrierV1_finite_abs_lt_one
      (by simp) (by simp) k

theorem barrier_trials_abs_summable :
    Summable (fun k => |barrierP2 k|) ∧ Summable (fun k => |barrierV2 k|) ∧
    Summable (fun k => |barrierP1 k|) ∧ Summable (fun k => |barrierV1 k|) := by
  have hg : Summable (fun k : ℕ => (15 : ℝ) * (99 / 100 : ℝ) ^ k) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(99 / 100 : ℝ)‖ < 1)).mul_left 15
  refine ⟨hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.1),
    hg.of_norm_bounded (by intro k; simpa using (barrier_trials_abs_le k).2.2.2)⟩


private theorem summable_barrier_weighted_square (u : ℕ → ℝ)
    (hu : ∀ k, |u k| ≤ 15 * (99 / 100 : ℝ) ^ k)
    (hs : Summable (fun k => |u k|)) :
    Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have ht : Summable (fun k : ℕ => |u (k + 1)|) :=
    (summable_nat_add_iff 1).mpr hs
  apply (ht.mul_left 15).of_norm_bounded
  intro k
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk
  have h15 : |u (k + 1)| ≤ 15 := by
    have hp : (99 / 100 : ℝ) ^ (k + 1) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hh := (hu (k + 1)).trans (mul_le_mul_of_nonneg_left hp (by norm_num))
    simpa only [mul_one] using hh
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hkp]
  calc
    _ ≤ |u (k + 1)| ^ 2 := div_le_self (sq_nonneg _) hk
    _ ≤ 15 * |u (k + 1)| := by
      simpa only [pow_two] using mul_le_mul_of_nonneg_right h15 (abs_nonneg (u (k + 1)))

theorem barrier_trials_norm_summable :
    Summable (fun k : ℕ => barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierP1 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ∧
    Summable (fun k : ℕ => barrierV1 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  exact ⟨summable_barrier_weighted_square barrierP2
      (fun k => (barrier_trials_abs_le k).1) barrier_trials_abs_summable.1,
    summable_barrier_weighted_square barrierV2
      (fun k => (barrier_trials_abs_le k).2.1) barrier_trials_abs_summable.2.1,
    summable_barrier_weighted_square barrierP1
      (fun k => (barrier_trials_abs_le k).2.2.1) barrier_trials_abs_summable.2.2.1,
    summable_barrier_weighted_square barrierV1
      (fun k => (barrier_trials_abs_le k).2.2.2) barrier_trials_abs_summable.2.2.2⟩


open Polynomial Filter
open scoped BigOperators










end

section

open scoped BigOperators




theorem barrierTrialNormSq_le_prefix_add_geometric_tail
    (u : ℕ → ℝ) (K : ℕ) (r B : ℝ)
    (hs : Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)))
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hB : 0 ≤ B)
    (htail : ∀ j : ℕ, |u (j + K + 1)| ≤ B * r ^ j) :
    barrierTrialNormSq u ≤
      (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        B ^ 2 / (((K + 1 : ℕ) : ℝ) * (1 - r ^ 2)) := by
  have hK : (0 : ℝ) < ((K + 1 : ℕ) : ℝ) := by positivity
  have hr2 : r ^ 2 < 1 := by
    nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr1.le)]
  have hshift : Summable (fun j : ℕ =>
      u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ)) :=
    (summable_nat_add_iff K).mpr hs
  have hpoint (j : ℕ) :
      u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ) ≤
        (B ^ 2 / ((K + 1 : ℕ) : ℝ)) * (r ^ 2) ^ j := by
    have hb : 0 ≤ B * r ^ j := mul_nonneg hB (pow_nonneg hr0 j)
    have hu : u (j + K + 1) ^ 2 ≤ (B * r ^ j) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (u (j + K + 1))) hb).mpr (htail j)
    have hd : ((K + 1 : ℕ) : ℝ) ≤ ((j + K + 1 : ℕ) : ℝ) := by
      simp only [Nat.cast_add, Nat.cast_one]
      linarith [show (0 : ℝ) ≤ (j : ℝ) from Nat.cast_nonneg j]
    have hpow : (r ^ j) ^ 2 = (r ^ 2) ^ j := by
      simp only [← pow_mul, Nat.mul_comm]
    calc
      _ ≤ (B * r ^ j) ^ 2 / ((j + K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right hu (Nat.cast_nonneg _)
      _ ≤ (B * r ^ j) ^ 2 / ((K + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hK hd
      _ = _ := by rw [mul_pow, hpow]; ring
  have hgeom := (hasSum_geometric_of_lt_one (sq_nonneg r) hr2).mul_left
    (B ^ 2 / ((K + 1 : ℕ) : ℝ))
  have hbound := hasSum_le hpoint hshift.hasSum hgeom
  have hsplit := Summable.sum_add_tsum_nat_add K hs
  unfold barrierTrialNormSq
  calc
    _ = (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        ∑' j : ℕ, u (j + K + 1) ^ 2 / ((j + K + 1 : ℕ) : ℝ) := hsplit.symm
    _ ≤ (∑ k ∈ Finset.range K, u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) +
        (B ^ 2 / ((K + 1 : ℕ) : ℝ)) * (1 - r ^ 2)⁻¹ :=
      add_le_add le_rfl hbound
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

end
section

open Polynomial
open scoped BigOperators



end

section

open Polynomial Set Filter
open scoped BigOperators



end

open Polynomial







open Polynomial
open scoped BigOperators





end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormPPrefix060
namespace OAI


noncomputable section

namespace InternalCatalan

def barrierP2MainBase : ℂ := barrierComplex (92 / 1000) (92 / 100)

theorem barrierConjugatePair_neg_star_power_re (z r : ℂ) (k : ℕ) :
    ((barrierConjugatePair (-star z) r).map
      (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ k)).sum.re =
      2 * (-1 : ℝ) ^ k * (r.re * (z ^ k).re + r.im * (z ^ k).im) := by
  rw [barrierConjugatePair_power_re]
  have hp : (-star z) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) * star (z ^ k) := by
    rw [Complex.ofReal_pow, neg_pow]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, star_pow]
  rw [hp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

def barrierP2CoefficientFormula (k : ℕ) (x y : ℝ) : ℝ :=
  barrierFiniteCoeff barrierP2Finite k +
  (-9338452 / 100000000) * (85 / 100) ^ k +
  (-2141509 / 100000000) * (94 / 100) ^ k +
  2 * barrierAxisPhase (-66277922 / 200000000) (31907569 / 200000000) k * (7 / 10) ^ k +
  2 * barrierAxisPhase (-1231651 / 200000000) (-6002645 / 200000000) k * (85 / 100) ^ k +
  2 * ((-3225918 / 200000000) * x - (-8928234 / 200000000) * y) +
  2 * (-1) ^ k * ((-2105536 / 200000000) * x + (9091287 / 200000000) * y)

theorem barrierP2_eq_coefficientFormula (k : ℕ) (hk : k ≠ 0) :
    barrierP2 k = barrierP2CoefficientFormula k
      (barrierP2MainBase ^ k).re (barrierP2MainBase ^ k).im := by
  have ho : barrierComplex (-92 / 1000) (92 / 100) = -star barrierP2MainBase := by
    apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex, Complex.star_def]
  simp only [barrierP2, barrierTrial, if_neg hk, barrierP2Tail,
    List.map_append, List.sum_append, Complex.add_re]
  rw [ho]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [barrierConjugatePair_neg_star_power_re]
  simp only [barrierConjugatePair_imaginary_power_re]
  simp only [barrierConjugatePair_power_re, barrierComplex_real_pow]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  change _ = barrierP2CoefficientFormula k
    ((barrierComplex (92 / 1000) (92 / 100)) ^ k).re
    ((barrierComplex (92 / 1000) (92 / 100)) ^ k).im
  norm_num [barrierP2CoefficientFormula, barrierP2MainBase, barrierComplex]
  ring





open scoped BigOperators

theorem barrierP2_exact_power_1 :
    barrierP2MainBase ^ 1 = barrierComplex (23 / 250) (23 / 25) := by
  norm_num [barrierP2MainBase, barrierComplex]

theorem barrierP2_norm_term_1 :
    barrierP2 1 ^ 2 / 1 < (32841741 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 1 (by norm_num), barrierP2_exact_power_1]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_2 :
    barrierP2MainBase ^ 2 = barrierComplex (-52371 / 62500) (529 / 3125) := by
  change barrierP2MainBase ^ (1 + 1) = _
  rw [pow_succ, barrierP2_exact_power_1]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_2 :
    barrierP2 2 ^ 2 / 2 < (17124183 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 2 (by norm_num), barrierP2_exact_power_2]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_3 :
    barrierP2MainBase ^ 3 = barrierComplex (-3637933 / 15625000) (-1180199 / 1562500) := by
  change barrierP2MainBase ^ (2 + 1) = _
  rw [pow_succ, barrierP2_exact_power_2]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_3 :
    barrierP2 3 ^ 2 / 3 < (1386970 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 3 (by norm_num), barrierP2_exact_power_3]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_4 :
    barrierP2MainBase ^ 4 = barrierComplex (2630785241 / 3906250000) (-27704259 / 97656250) := by
  change barrierP2MainBase ^ (3 + 1) = _
  rw [pow_succ, barrierP2_exact_power_3]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_4 :
    barrierP2 4 ^ 2 / 4 < (7952514 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 4 (by norm_num), barrierP2_exact_power_4]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_5 :
    barrierP2MainBase ^ 5 = barrierComplex (315387243343 / 976562500000) (11591853743 / 19531250000) := by
  change barrierP2MainBase ^ (4 + 1) = _
  rw [pow_succ, barrierP2_exact_power_4]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_5 :
    barrierP2 5 ^ 2 / 5 < (334056 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 5 (by norm_num), barrierP2_exact_power_5]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_6 :
    barrierP2MainBase ^ 6 = barrierComplex (-126052411447611 / 244140625000000) (4293484888667 / 12207031250000) := by
  change barrierP2MainBase ^ (5 + 1) = _
  rw [pow_succ, barrierP2_exact_power_5]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_6 :
    barrierP2 6 ^ 2 / 6 < (1082946 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 6 (by norm_num), barrierP2_exact_power_6]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_7 :
    barrierP2MainBase ^ 7 = barrierComplex (-22649235951163253 / 61035156250000000) (-2701705158416371 / 6103515625000000) := by
  change barrierP2MainBase ^ (6 + 1) = _
  rw [pow_succ, barrierP2_exact_power_6]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_7 :
    barrierP2 7 ^ 2 / 7 < (202802 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 7 (by norm_num), barrierP2_exact_power_7]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_8 :
    barrierP2MainBase ^ 8 = barrierComplex (5692989437480898481 / 15258789062500000000) (-72883955690041419 / 190734863281250000) := by
  change barrierP2MainBase ^ (7 + 1) = _
  rw [pow_succ, barrierP2_exact_power_7]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_8 :
    barrierP2 8 ^ 2 / 8 < (3030164 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 8 (by norm_num), barrierP2_exact_power_8]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_8 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (0 + k + 1) ^ 2 / ((0 + k + 1 : ℕ) : ℝ)) ≤
      (63955376 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_1.le) barrierP2_norm_term_2.le) barrierP2_norm_term_3.le) barrierP2_norm_term_4.le) barrierP2_norm_term_5.le) barrierP2_norm_term_6.le) barrierP2_norm_term_7.le) barrierP2_norm_term_8.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_8 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (63955376 / 1000000000 : ℝ) := by
  simpa only [Nat.zero_add] using barrierP2_norm_block_8

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_9 :
    barrierP2MainBase ^ 9 = barrierComplex (1472003541758822774663 / 3814697265625000000000) (117528109215093043967 / 381469726562500000000) := by
  change barrierP2MainBase ^ (8 + 1) = _
  rw [pow_succ, barrierP2_exact_power_8]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_9 :
    barrierP2 9 ^ 2 / 9 < (106660 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 9 (by norm_num), barrierP2_exact_power_9]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_10 :
    barrierP2MainBase ^ 10 = barrierComplex (-236458569734261077306851 / 953674316406250000000000) (3655922797240006382849 / 9536743164062500000000) := by
  change barrierP2MainBase ^ (9 + 1) = _
  rw [pow_succ, barrierP2_exact_power_9]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_10 :
    barrierP2 10 ^ 2 / 10 < (490838 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 10 (by norm_num), barrierP2_exact_power_10]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_11 :
    barrierP2MainBase ^ 11 = barrierComplex (-89524771440408151583584573 / 238418579101562500000000000) (-4597684860522803310002303 / 23841857910156250000000000) := by
  change barrierP2MainBase ^ (10 + 1) = _
  rw [pow_succ, barrierP2_exact_power_10]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_11 :
    barrierP2 11 ^ 2 / 11 < (59971 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 11 (by norm_num), barrierP2_exact_power_11]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_12 :
    barrierP2MainBase ^ 12 = barrierComplex (8515605436073060126582851721 / 59604644775390625000000000000) (-541204123730352990638124537 / 1490116119384765625000000000) := by
  change barrierP2MainBase ^ (11 + 1) = _
  rw [pow_succ, barrierP2_exact_power_11]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_12 :
    barrierP2 12 ^ 2 / 12 < (962373 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 12 (by norm_num), barrierP2_exact_power_12]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_13 :
    barrierP2MainBase ^ 13 = barrierComplex (5174936863348927896782151329983 / 14901161193847656250000000000000) (146068145646487907772698132179 / 1490116119384765625000000000000) := by
  change barrierP2MainBase ^ (12 + 1) = _
  rw [pow_succ, barrierP2_exact_power_12]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_13 :
    barrierP2 13 ^ 2 / 13 < (33139 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 13 (by norm_num), barrierP2_exact_power_13]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_14 :
    barrierP2MainBase ^ 14 = barrierComplex (-216933187129896846251216223422091 / 3725290298461914062500000000000000) (61191557603447281752380768814863 / 186264514923095703125000000000000) := by
  change barrierP2MainBase ^ (13 + 1) = _
  rw [pow_succ, barrierP2_exact_power_13]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_14 :
    barrierP2 14 ^ 2 / 14 < (174740 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 14 (by norm_num), barrierP2_exact_power_14]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_15 :
    barrierP2MainBase ^ 15 = barrierComplex (-286470628279845123524729509687077893 / 931322574615478515625000000000000000) (-434930330845810500633691554644879 / 18626451492309570312500000000000000) := by
  change barrierP2MainBase ^ (14 + 1) = _
  rw [pow_succ, barrierP2_exact_power_14]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_15 :
    barrierP2 15 ^ 2 / 15 < (18967 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 15 (by norm_num), barrierP2_exact_power_15]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_16 :
    barrierP2MainBase ^ 16 = barrierComplex (-1587125645709617083781325844386683039 / 232830643653869628906250000000000000000) (-414927589905231628040103328224184539 / 1455191522836685180664062500000000000) := by
  change barrierP2MainBase ^ (15 + 1) = _
  rw [pow_succ, barrierP2_exact_power_15]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_16 :
    barrierP2 16 ^ 2 / 16 < (297779 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 16 (by norm_num), barrierP2_exact_power_16]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_16 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (8 + k + 1) ^ 2 / ((8 + k + 1 : ℕ) : ℝ)) ≤
      (2144467 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_9.le) barrierP2_norm_term_10.le) barrierP2_norm_term_11.le) barrierP2_norm_term_12.le) barrierP2_norm_term_13.le) barrierP2_norm_term_14.le) barrierP2_norm_term_15.le) barrierP2_norm_term_16.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_16 :
    (∑ k ∈ Finset.range 16,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66099843 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (8 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_8 barrierP2_norm_block_16
  have hc : (63955376 / 1000000000 : ℝ) + 2144467 / 1000000000 =
      66099843 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_17 :
    barrierP2MainBase ^ 17 = barrierComplex (15232831418661202718948831984229097325303 / 58207660913467407226562500000000000000000) (-189197242936446432045728519207393620249 / 5820766091346740722656250000000000000000) := by
  change barrierP2MainBase ^ (16 + 1) = _
  rw [pow_succ, barrierP2_exact_power_16]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_17 :
    barrierP2 17 ^ 2 / 17 < (10260 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 17 (by norm_num), barrierP2_exact_power_17]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_18 :
    barrierP2MainBase ^ 18 = barrierComplex (785508781383034456240998729814274565054669 / 14551915228366851806640625000000000000000000) (173001793020834697299385689847749592608121 / 727595761418342590332031250000000000000000) := by
  change barrierP2MainBase ^ (17 + 1) = _
  rw [pow_succ, barrierP2_exact_power_17]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_18 :
    barrierP2 18 ^ 2 / 18 < (48895 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 18 (by norm_num), barrierP2_exact_power_18]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_19 :
    barrierP2MainBase ^ 19 = barrierComplex (-777741545924029815083631202513919811001099213 / 3637978807091712951660156250000000000000000000) (26024784450768188569314712518724796256230953 / 363797880709171295166015625000000000000000000) := by
  change barrierP2MainBase ^ (18 + 1) = _
  rw [pow_succ, barrierP2_exact_power_18]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_19 :
    barrierP2 19 ^ 2 / 19 < (6325 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 19 (by norm_num), barrierP2_exact_power_19]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_20 :
    barrierP2MainBase ^ 20 = barrierComplex (-77745059793019519456347356450887187042356473799 / 909494701772928237915039062500000000000000000000) (-864474275694250870491463963494474266956598499 / 4547473508864641189575195312500000000000000000) := by
  change barrierP2MainBase ^ (19 + 1) = _
  rw [pow_succ, barrierP2_exact_power_19]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_20 :
    barrierP2 20 ^ 2 / 20 < (82159 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 20 (by norm_num), barrierP2_exact_power_20]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_21 :
    barrierP2MainBase ^ 21 = barrierComplex (37977680306696091095111353122375410978029332056623 / 227373675443232059478759765625000000000000000000000) (-2185794542058804347922062621577863464774234206917 / 22737367544323205947875976562500000000000000000000) := by
  change barrierP2MainBase ^ (20 + 1) = _
  rw [pow_succ, barrierP2_exact_power_20]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_21 :
    barrierP2 21 ^ 2 / 21 < (3715 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 21 (by norm_num), barrierP2_exact_power_21]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_22 :
    barrierP2MainBase ^ 22 = barrierComplex (5900814093789260095408305151443720421475413313211429 / 56843418860808014869689941406250000000000000000000000) (411606686293328797592676840759171796402433625271619 / 2842170943040400743484497070312500000000000000000000) := by
  change barrierP2MainBase ^ (21 + 1) = _
  rw [pow_succ, barrierP2_exact_power_21]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_22 :
    barrierP2 22 ^ 2 / 22 < (7755 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 22 (by norm_num), barrierP2_exact_power_22]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_23 :
    barrierP2MainBase ^ 23 = barrierComplex (-1757672032792159486731922449008984693757260170045584533 / 14210854715202003717422485351562500000000000000000000000) (154652631726646106883654153158127472328446452966357341 / 1421085471520200371742248535156250000000000000000000000) := by
  change barrierP2MainBase ^ (22 + 1) = _
  rw [pow_succ, barrierP2_exact_power_22]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_23 :
    barrierP2 23 ^ 2 / 23 < (2457 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 23 (by norm_num), barrierP2_exact_power_23]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_24 :
    barrierP2MainBase ^ 24 = barrierComplex (-396127509725505714027238768590899834311843825733670328559 / 3552713678800500929355621337890625000000000000000000000000) (-4608680778063350967063771350571214511607839436602778177 / 44408920985006261616945266723632812500000000000000000000) := by
  change barrierP2MainBase ^ (23 + 1) = _
  rw [pow_succ, barrierP2_exact_power_23]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_24 :
    barrierP2 24 ^ 2 / 24 < (16454 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 24 (by norm_num), barrierP2_exact_power_24]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_24 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (16 + k + 1) ^ 2 / ((16 + k + 1 : ℕ) : ℝ)) ≤
      (178020 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_17.le) barrierP2_norm_term_18.le) barrierP2_norm_term_19.le) barrierP2_norm_term_20.le) barrierP2_norm_term_21.le) barrierP2_norm_term_22.le) barrierP2_norm_term_23.le) barrierP2_norm_term_24.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_24 :
    (∑ k ∈ Finset.range 24,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66277863 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (16 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_16 barrierP2_norm_block_24
  have hc : (66099843 / 1000000000 : ℝ) + 178020 / 1000000000 =
      66277863 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_25 :
    barrierP2MainBase ^ 25 = barrierComplex (75688793592679026371346901172919650824411837641616700899943 / 888178419700125232338905334472656250000000000000000000000000) (-398357199474011520022649024243831986372330017928373149657 / 3552713678800500929355621337890625000000000000000000000000) := by
  change barrierP2MainBase ^ (24 + 1) = _
  rw [pow_succ, barrierP2_exact_power_24]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_25 :
    barrierP2 25 ^ 2 / 25 < (1416 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 25 (by norm_num), barrierP2_exact_power_25]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_26 :
    barrierP2MainBase ^ 26 = barrierComplex (24646381222387280007843297620997491185370448296638640225976189 / 222044604925031308084726333618164062500000000000000000000000000) (755893431467030491263977769018474288398691252724184779822957 / 11102230246251565404236316680908203125000000000000000000000000) := by
  change barrierP2MainBase ^ (25 + 1) = _
  rw [pow_succ, barrierP2_exact_power_25]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_26 :
    barrierP2 26 ^ 2 / 26 < (35 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 26 (by norm_num), barrierP2_exact_power_26]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_27 :
    barrierP2MainBase ^ 27 = barrierComplex (-2910243016633432819633901892202039429370459451708561261988149853 / 55511151231257827021181583404541015625000000000000000000000000000) (601637865962390842778538822657792114529860108448001225069308369 / 5551115123125782702118158340454101562500000000000000000000000000) := by
  change barrierP2MainBase ^ (26 + 1) = _
  rw [pow_succ, barrierP2_exact_power_26]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_27 :
    barrierP2 27 ^ 2 / 27 < (1122 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 27 (by norm_num), barrierP2_exact_power_27]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_28 :
    barrierP2MainBase ^ 28 = barrierComplex (-1450702681096067893242219035633568770294198816819699726685136695319 / 13877787807814456755295395851135253906250000000000000000000000000000) (-13274479616358491366918337649879422060333446223748220212283338533 / 346944695195361418882384896278381347656250000000000000000000000000) := by
  change barrierP2MainBase ^ (27 + 1) = _
  rw [pow_succ, barrierP2_exact_power_27]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_28 :
    barrierP2 28 ^ 2 / 28 < (1398 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 28 (by norm_num), barrierP2_exact_power_28]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_29 :
    barrierP2MainBase ^ 29 = barrierComplex (88759050805288559031077668559318601238301132471630532239248570511263 / 3469446951953614188823848962783813476562500000000000000000000000000000) (-34587413789914542750327524883360988546317249839437929973288211137373 / 346944695195361418882384896278381347656250000000000000000000000000000) := by
  change barrierP2MainBase ^ (28 + 1) = _
  rw [pow_succ, barrierP2_exact_power_28]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_29 :
    barrierP2 29 ^ 2 / 29 < (550 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 29 (by norm_num), barrierP2_exact_power_29]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_30 :
    barrierP2MainBase ^ 30 = barrierComplex (81592509885325085183468093608594601485010600677554741180065602737716949 / 867361737988403547205962240695953369140625000000000000000000000000000000) (124594765135360237445725330454702509191562930054042985211708826559947 / 8673617379884035472059622406959533691406250000000000000000000000000000) := by
  change barrierP2MainBase ^ (29 + 1) = _
  rw [pow_succ, barrierP2_exact_power_29]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_30 :
    barrierP2 30 ^ 2 / 30 < (1356 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 30 (by norm_num), barrierP2_exact_power_30]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_31 :
    barrierP2MainBase ^ 31 = barrierComplex (-989051870750808502031916447460481877250703575659229612727794147911291173 / 216840434497100886801490560173988342285156250000000000000000000000000000000) (1905284523343609813832282979002257411269303289496188933740201893076277637 / 21684043449710088680149056017398834228515625000000000000000000000000000000) := by
  change barrierP2MainBase ^ (30 + 1) = _
  rw [pow_succ, barrierP2_exact_power_30]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_31 :
    barrierP2 31 ^ 2 / 31 < (577 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 31 (by norm_num), barrierP2_exact_power_31]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_32 :
    barrierP2MainBase ^ 32 = barrierComplex (-4404902596717571167360984929996783129096163748081396828695203619477398262079 / 54210108624275221700372640043497085571289062500000000000000000000000000000000) (658542219051075942856513444545651165075868544320314511977668066837334021 / 169406589450860067813664500135928392410278320312500000000000000000000000000) := by
  change barrierP2MainBase ^ (31 + 1) = _
  rw [pow_succ, barrierP2_exact_power_31]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_32 :
    barrierP2 32 ^ 2 / 32 < (69 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 32 (by norm_num), barrierP2_exact_power_32]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_32 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (24 + k + 1) ^ 2 / ((24 + k + 1 : ℕ) : ℝ)) ≤
      (6523 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_25.le) barrierP2_norm_term_26.le) barrierP2_norm_term_27.le) barrierP2_norm_term_28.le) barrierP2_norm_term_29.le) barrierP2_norm_term_30.le) barrierP2_norm_term_31.le) barrierP2_norm_term_32.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_32 :
    (∑ k ∈ Finset.range 32,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66284386 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (24 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_24 barrierP2_norm_block_32
  have hc : (66277863 / 1000000000 : ℝ) + 6523 / 1000000000 =
      66284386 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_33 :
    barrierP2MainBase ^ 33 = barrierComplex (-149781467046663326243542042908485937718795691067847275141546052967207943973417 / 13552527156068805425093160010874271392822265625000000000000000000000000000000000) (-100828072651282544955360259494740412711715926957252375579174119550787882188361 / 1355252715606880542509316001087427139282226562500000000000000000000000000000000) := by
  change barrierP2MainBase ^ (32 + 1) = _
  rw [pow_succ, barrierP2_exact_power_32]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_33 :
    barrierP2 33 ^ 2 / 33 < (220 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 33 (by norm_num), barrierP2_exact_power_33]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_34 :
    barrierP2MainBase ^ 34 = barrierComplex (228459593355876596893727129851007772669414331107119976503844915748566346321841709 / 3388131789017201356273290002718567848205566406250000000000000000000000000000000000) (-2882009706526377518787376477637103029950883607288645983288281983956952000860447 / 169406589450860067813664500135928392410278320312500000000000000000000000000000000) := by
  change barrierP2MainBase ^ (33 + 1) = _
  rw [pow_succ, barrierP2_exact_power_33]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_34 :
    barrierP2 34 ^ 2 / 34 < (2707 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 34 (by norm_num), barrierP2_exact_power_34]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_35 :
    barrierP2MainBase ^ 35 = barrierComplex (18511815297206498314977655783703852709170594208991530982714530188419005169360415507 / 847032947254300339068322500679641962051391601562500000000000000000000000000000000000) (1024399640136989672538300933720374406403757793905696348871434418191001234672555749 / 16940658945086006781366450013592839241027832031250000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (34 + 1) = _
  rw [pow_succ, barrierP2_exact_power_34]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_35 :
    barrierP2 35 ^ 2 / 35 < (315 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 35 (by norm_num), barrierP2_exact_power_35]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_36 :
    barrierP2MainBase ^ 36 = barrierComplex (-11354824109739631772945974654759117061332290963108702799419061614862877079839101556839 / 211758236813575084767080625169910490512847900390625000000000000000000000000000000000000) (135894427612875818396597672600757917261838953276490073180662288106400565220658366949 / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (35 + 1) = _
  rw [pow_succ, barrierP2_exact_power_35]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_36 :
    barrierP2 36 ^ 2 / 36 < (659 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 36 (by norm_num), barrierP2_exact_power_36]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_37 :
    barrierP2MainBase ^ 37 = barrierComplex (-1511389688562469060026456004986432531219561062295208837648731467720731372866356311738097 / 52939559203393771191770156292477622628211975097656250000000000000000000000000000000000000) (-248658667183626955485270431180189964022553508450063077654017486636057320835998766047989 / 5293955920339377119177015629247762262821197509765625000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (36 + 1) = _
  rw [pow_succ, barrierP2_exact_power_36]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_37 :
    barrierP2 37 ^ 2 / 37 < (94 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 37 (by norm_num), barrierP2_exact_power_37]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_38 :
    barrierP2MainBase ^ 38 = barrierComplex (537152971685405209235513503599748969033823165002355275338319395505355016346870966740398469 / 13234889800848442797942539073119405657052993774414062500000000000000000000000000000000000000) (-20240556091080104178384854015916158695284317563570627025981612975103069977577083394539989 / 661744490042422139897126953655970282852649688720703125000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (37 + 1) = _
  rw [pow_succ, barrierP2_exact_power_37]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_38 :
    barrierP2 38 ^ 2 / 38 < (2571 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 38 (by norm_num), barrierP2_exact_power_38]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_39 :
    barrierP2MainBase ^ 39 = barrierComplex (105461076367732799032987139056008556286085793587479055652296765782097287272832615849913114187 / 3308722450212110699485634768279851414263248443603515625000000000000000000000000000000000000000) (11423452768574635020211107298062082987794854187129922489586191899768424157009486398880325293 / 330872245021211069948563476827985141426324844360351562500000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (38 + 1) = _
  rw [pow_succ, barrierP2_exact_power_38]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_39 :
    barrierP2 39 ^ 2 / 39 < (174 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 39 (by norm_num), barrierP2_exact_power_39]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_40 :
    barrierP2MainBase ^ 40 = barrierComplex (-23848336611263806168726842587254594077348191377886803446045415756479137953846668552876746547599 / 827180612553027674871408692069962853565812110900878906250000000000000000000000000000000000000000) (67208604253376774580588991653590617582481372470400162431582700667072784072159208793056227701 / 2067951531382569187178521730174907133914530277252197265625000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (39 + 1) = _
  rw [pow_succ, barrierP2_exact_power_39]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_40 :
    barrierP2 40 ^ 2 / 40 < (738 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 40 (by norm_num), barrierP2_exact_power_40]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_40 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (32 + k + 1) ^ 2 / ((32 + k + 1 : ℕ) : ℝ)) ≤
      (7478 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_33.le) barrierP2_norm_term_34.le) barrierP2_norm_term_35.le) barrierP2_norm_term_36.le) barrierP2_norm_term_37.le) barrierP2_norm_term_38.le) barrierP2_norm_term_39.le) barrierP2_norm_term_40.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_40 :
    (∑ k ∈ Finset.range 40,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66291864 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (32 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_32 barrierP2_norm_block_40
  have hc : (66284386 / 1000000000 : ℝ) + 7478 / 1000000000 =
      66291864 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_41 :
    barrierP2MainBase ^ 41 = barrierComplex (-6731703333369730803294904611637192481367294668968211422964653023769716307577120585677338119086777 / 206795153138256918717852173017490713391453027725219726562500000000000000000000000000000000000000000) (-486679826145960909266575507185552295603125539018628329821988477785313211592086904626553441109857 / 20679515313825691871785217301749071339145302772521972656250000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (40 + 1) = _
  rw [pow_succ, barrierP2_exact_power_40]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_41 :
    barrierP2 41 ^ 2 / 41 < (44 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 41 (by norm_num), barrierP2_exact_power_41]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_42 :
    barrierP2MainBase ^ 42 = barrierComplex (964534423468206282837340860459114852815740962356576295862386479359516911587526107170494137813675229 / 51698788284564229679463043254372678347863256931304931640625000000000000000000000000000000000000000000) (-83011406334430454694457021366461564935159832391848657157046377267882839470445886138494752942261291 / 2584939414228211483973152162718633917393162846565246582031250000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (41 + 1) = _
  rw [pow_succ, barrierP2_exact_power_41]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_42 :
    barrierP2 42 ^ 2 / 42 < (1705 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 42 (by norm_num), barrierP2_exact_power_42]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_43 :
    barrierP2MainBase ^ 43 = barrierComplex (404036760878148836099761138076282840316497271136705077727248224457529950530564176701997228704116468867 / 12924697071141057419865760813593169586965814232826232910156250000000000000000000000000000000000000000000) (18365767048384943589313816807702409627744689844176216575610755670946278350872589702550606534370510881 / 1292469707114105741986576081359316958696581423282623291015625000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (42 + 1) = _
  rw [pow_succ, barrierP2_exact_power_42]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_43 :
    barrierP2 43 ^ 2 / 43 < (95 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 43 (by norm_num), barrierP2_exact_power_43]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_44 :
    barrierP2MainBase ^ 44 = barrierComplex (-32948418711087947025127272481961036816533349405461081336178028880653251344803980251720458768857496242359 / 3231174267785264354966440203398292396741453558206558227539062500000000000000000000000000000000000000000000) (2428814535577569233212180990582915187179391275640067442241439135738738316068261406826150052621300133551 / 80779356694631608874161005084957309918536338955163955688476562500000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (43 + 1) = _
  rw [pow_succ, barrierP2_exact_power_43]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_44 :
    barrierP2 44 ^ 2 / 44 < (455 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 44 (by norm_num), barrierP2_exact_power_44]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_45 :
    barrierP2MainBase ^ 45 = barrierComplex (-23102907357668659727129992380447923568830666772214225339353334713051417288758496488590151035799683642243457 / 807793566946316088741610050849573099185363389551639556884765625000000000000000000000000000000000000000000000) (-106872538616377282424481323190295129911952607793343733209176452753412171170442299272312949368512560257513 / 16155871338926321774832201016991461983707267791032791137695312500000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (44 + 1) = _
  rw [pow_succ, barrierP2_exact_power_44]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_45 :
    barrierP2 45 ^ 2 / 45 < (23 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 45 (by norm_num), barrierP2_exact_power_45]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_46 :
    barrierP2MainBase ^ 46 = barrierComplex (697667324861959574157545391938091751904349653862525749100402508264057370818641022394025443914501719189799989 / 201948391736579022185402512712393274796340847387909889221191406250000000000000000000000000000000000000000000000) (-271828605583631280601402588458593091011489942828580856062090995233412498663023141826944731500385834100606753 / 10097419586828951109270125635619663739817042369395494461059570312500000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (45 + 1) = _
  rw [pow_succ, barrierP2_exact_power_45]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_46 :
    barrierP2 46 ^ 2 / 46 < (870 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 46 (by norm_num), barrierP2_exact_power_46]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_47 :
    barrierP2MainBase ^ 47 = barrierComplex (1266457934156528960972075450924104328946653779050310030114927835763770813378735195919008350111808376404156463547 / 50487097934144755546350628178098318699085211846977472305297851562500000000000000000000000000000000000000000000000) (3542232614978031297959024945480828107271504668723372850453071909336344590329678991023127561015791172737489109 / 5048709793414475554635062817809831869908521184697747230529785156250000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (46 + 1) = _
  rw [pow_succ, barrierP2_exact_power_46]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_47 :
    barrierP2 47 ^ 2 / 47 < (50 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 47 (by norm_num), barrierP2_exact_power_47]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_48 :
    barrierP2MainBase ^ 48 = barrierComplex (20981397471150694117051977996648494919048576180093373136601274831093136149952647826783998662235272959999373710881 / 12621774483536188886587657044524579674771302961744368076324462890625000000000000000000000000000000000000000000000000) (1825625239734041301388174559062528663265017595346110516762735054780091539580530757683170249154684740891785056943 / 78886090522101180541172856528278622967320643510902300477027893066406250000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (47 + 1) = _
  rw [pow_succ, barrierP2_exact_power_47]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_48 :
    barrierP2 48 ^ 2 / 48 < (181 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 48 (by norm_num), barrierP2_exact_power_48]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_48 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (40 + k + 1) ^ 2 / ((40 + k + 1 : ℕ) : ℝ)) ≤
      (3423 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_41.le) barrierP2_norm_term_42.le) barrierP2_norm_term_43.le) barrierP2_norm_term_44.le) barrierP2_norm_term_45.le) barrierP2_norm_term_46.le) barrierP2_norm_term_47.le) barrierP2_norm_term_48.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_48 :
    (∑ k ∈ Finset.range 48,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295287 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (40 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_40 barrierP2_norm_block_48
  have hc : (66291864 / 1000000000 : ℝ) + 3423 / 1000000000 =
      66295287 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_49 :
    barrierP2MainBase ^ 49 = barrierComplex (-66700436680376253926392628279578139425014530256594719434726820694792226525114620982724633199660987186737704500152137 / 3155443620884047221646914261131144918692825740436092019081115722656250000000000000000000000000000000000000000000000000) (1154402230058593163603043731657925931219643727229516252310515821274215818014546218843438620920335262728162496305287 / 315544362088404722164691426113114491869282574043609201908111572265625000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (48 + 1) = _
  rw [pow_succ, barrierP2_exact_power_48]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_49 :
    barrierP2 49 ^ 2 / 49 < (14 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 49 (by norm_num), barrierP2_exact_power_49]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_50 :
    barrierP2MainBase ^ 50 = barrierComplex (-4189235172783418116594031033243526848580514768529565927312903264910917591511092585942575391708973809569740945005659251 / 788860905221011805411728565282786229673206435109023004770278930664062500000000000000000000000000000000000000000000000000) (-30151175847146123950883208892043298207145647803507993463911500241818284925266034391385349506220699885044389321769551 / 1577721810442023610823457130565572459346412870218046009540557861328125000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (49 + 1) = _
  rw [pow_succ, barrierP2_exact_power_49]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_50 :
    barrierP2 50 ^ 2 / 50 < (346 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 50 (by norm_num), barrierP2_exact_power_50]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_51 :
    barrierP2MainBase ^ 51 = barrierComplex (3371032813447785637669906308820378176304397657727239232021625752716151661800838825532635959206074089160000730268368202227 / 197215226305252951352932141320696557418301608777255751192569732666015625000000000000000000000000000000000000000000000000000) (-131026261198236659225178403990450910455569334650214208811695000371042132268811069026772385941460202487905089455165146423 / 19721522630525295135293214132069655741830160877725575119256973266601562500000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (50 + 1) = _
  rw [pow_succ, barrierP2_exact_power_50]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_51 :
    barrierP2 51 ^ 2 / 51 < (26 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 51 (by norm_num), barrierP2_exact_power_51]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_52 :
    barrierP2MainBase ^ 52 = barrierComplex (378894155465243385884318174280905792102810615823219182603395893165868392439684751748827114727098169772861722543052305424121 / 49303806576313237838233035330174139354575402194313937798142433166503906250000000000000000000000000000000000000000000000000000) (18630037675434906626057185452772081778630762857692893883457101825984379794809159599908715546271529848364549934675917570873 / 1232595164407830945955825883254353483864385054857848444953560829162597656250000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (51 + 1) = _
  rw [pow_succ, barrierP2_exact_power_51]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_52 :
    barrierP2 52 ^ 2 / 52 < (40 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 52 (by norm_num), barrierP2_exact_power_52]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_53 :
    barrierP2MainBase ^ 53 = barrierComplex (-162681781038300543084386788157042319145038374126840582527927231256241321086131519028937159386974816700178039780528238627276817 / 12325951644078309459558258832543534838643850548578484449535608291625976562500000000000000000000000000000000000000000000000000000) (10428529041840609284936579070115864741998674346841787437156158910805535967235191973414625468980238650825358212480387441275099 / 1232595164407830945955825883254353483864385054857848444953560829162597656250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (52 + 1) = _
  rw [pow_succ, barrierP2_exact_power_52]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_53 :
    barrierP2 53 ^ 2 / 53 < (9 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 53 (by norm_num), barrierP2_exact_power_53]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_54 :
    barrierP2MainBase ^ 54 = barrierComplex (-27727297760114313846295027988878462246932833602653444503601491813746283109621966476519193244554969681002418803657040603360094491 / 3081487911019577364889564708135883709660962637144621112383902072906494140625000000000000000000000000000000000000000000000000000000) (-1750912397959289238693677404499654225634956547469986143543867331972511528867307761138509140056937647567555838032550288639019757 / 154074395550978868244478235406794185483048131857231055619195103645324707031250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (53 + 1) = _
  rw [pow_succ, barrierP2_exact_power_53]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_54 :
    barrierP2 54 ^ 2 / 54 < (102 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 54 (by norm_num), barrierP2_exact_power_54]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_55 :
    barrierP2MainBase ^ 55 = barrierComplex (7416469182130101279526130416954204806241344945500907036718955415357388521268310472277200599637148876147701222465619393862208708907 / 770371977754894341222391177033970927415240659286155278095975518226623535156250000000000000000000000000000000000000000000000000000000) (-143653963757751304688938960870237745211732634808929717237170441797380008369840277194462573013476686890232640206721849430935416423 / 15407439555097886824447823540679418548304813185723105561919510364532470703125000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (54 + 1) = _
  rw [pow_succ, barrierP2_exact_power_54]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_55 :
    barrierP2 55 ^ 2 / 55 < (13 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 55 (by norm_num), barrierP2_exact_power_55]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_56 :
    barrierP2MainBase ^ 56 = barrierComplex (1822599374403132333351899049597680780478476234049212610071996055223090032242334328598695203446636323389072490494010514514588089169361 / 192592994438723585305597794258492731853810164821538819523993879556655883789062500000000000000000000000000000000000000000000000000000000) (19257323169606366173734127386233671230525210092936743045282671718315154378329938623126552236888075644877546811617029171784153427027 / 2407412430484044816319972428231159148172627060269235244049923494458198547363281250000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (55 + 1) = _
  rw [pow_succ, barrierP2_exact_power_55]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_56 :
    barrierP2 56 ^ 2 / 56 < (2 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 56 (by norm_num), barrierP2_exact_power_56]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_56 :
    (∑ k ∈ Finset.range 8,
      barrierP2 (48 + k + 1) ^ 2 / ((48 + k + 1 : ℕ) : ℝ)) ≤
      (552 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_49.le) barrierP2_norm_term_50.le) barrierP2_norm_term_51.le) barrierP2_norm_term_52.le) barrierP2_norm_term_53.le) barrierP2_norm_term_54.le) barrierP2_norm_term_55.le) barrierP2_norm_term_56.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_56 :
    (∑ k ∈ Finset.range 56,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295839 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (48 + 8),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_48 barrierP2_norm_block_56
  have hc : (66295287 / 1000000000 : ℝ) + 552 / 1000000000 =
      66295839 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierP2_exact_power_57 :
    barrierP2MainBase ^ 57 = barrierComplex (-312414960709485093929614265765952892690658912326904182001545250346867769819697181107758571479467956427798194052391094926992897006401497 / 48148248609680896326399448564623182963452541205384704880998469889163970947265625000000000000000000000000000000000000000000000000000000000) (45463133074479615043060757579813653457421592040232250751987920866301059147186398264425275290860041356606135894699775201443810281468271 / 4814824860968089632639944856462318296345254120538470488099846988916397094726562500000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (56 + 1) = _
  rw [pow_succ, barrierP2_exact_power_56]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_57 :
    barrierP2 57 ^ 2 / 57 < (6 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 57 (by norm_num), barrierP2_exact_power_57]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_58 :
    barrierP2MainBase ^ 58 = barrierComplex (-111750750167621271759420870546188319483954816676052972915607758750470394744381751173656580313005858118033471021014478146641600278524257731 / 12037062152420224081599862141155795740863135301346176220249617472290992736816406250000000000000000000000000000000000000000000000000000000000) (-3069946017802563007195365344140601251182229183296727209369909289026517172733874002698332906168991023318708668813450176843814497336732099 / 601853107621011204079993107057789787043156765067308811012480873614549636840820312500000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (57 + 1) = _
  rw [pow_succ, barrierP2_exact_power_57]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_58 :
    barrierP2 58 ^ 2 / 58 < (19 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 58 (by norm_num), barrierP2_exact_power_58]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_59 :
    barrierP2MainBase ^ 59 = barrierComplex (11551484428036500582632000560484434407307293459615726786042604278261159915455040135418230021178223970551290043058537816108789881342909727587 / 3009265538105056020399965535288948935215783825336544055062404368072748184204101562500000000000000000000000000000000000000000000000000000000000) (-2711484770674207148797666828392799005685343325980867828689994278556038869066538481118224660882908323787430432248751705507572273283547604367 / 300926553810505602039996553528894893521578382533654405506240436807274818420410156250000000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (58 + 1) = _
  rw [pow_succ, barrierP2_exact_power_58]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_59 :
    barrierP2 59 ^ 2 / 59 < (7 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 59 (by norm_num), barrierP2_exact_power_59]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_exact_power_60 :
    barrierP2MainBase ^ 60 = barrierComplex (6502099114395515955635169718194579704444357399327157722065966739078896076908504429686536010517788296033769665162475292437918395823046413778601 / 752316384526264005099991383822237233803945956334136013765601092018187046051025390625000000000000000000000000000000000000000000000000000000000000) (10165999605966637448909483791905380711865242653680087800955501499660889203346776902445006164339612993778438552431254027191400249268266441703 / 3761581922631320025499956919111186169019729781670680068828005460090935230255126953125000000000000000000000000000000000000000000000000000000000) := by
  change barrierP2MainBase ^ (59 + 1) = _
  rw [pow_succ, barrierP2_exact_power_59]
  apply Complex.ext <;> norm_num [barrierP2MainBase, barrierComplex,
    Complex.mul_re, Complex.mul_im]

theorem barrierP2_norm_term_60 :
    barrierP2 60 ^ 2 / 60 < (5 / 1000000000 : ℝ) := by
  rw [barrierP2_eq_coefficientFormula 60 (by norm_num), barrierP2_exact_power_60]
  norm_num [barrierP2CoefficientFormula, barrierFiniteCoeff,
    barrierP2Finite, barrierAxisPhase, barrierComplex,
    barrierI_pow_re_port, barrierI_pow_im_port]

theorem barrierP2_norm_block_60 :
    (∑ k ∈ Finset.range 4,
      barrierP2 (56 + k + 1) ^ 2 / ((56 + k + 1 : ℕ) : ℝ)) ≤
      (37 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierP2_norm_term_57.le) barrierP2_norm_term_58.le) barrierP2_norm_term_59.le) barrierP2_norm_term_60.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierP2_norm_prefix_60 :
    (∑ k ∈ Finset.range 60,
      barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (66295876 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (56 + 4),
    barrierP2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierP2_norm_prefix_56 barrierP2_norm_block_60
  have hc : (66295839 / 1000000000 : ℝ) + 37 / 1000000000 =
      66295876 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormVPrefix048
namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_1 :
    barrierV2 1 ^ 2 / 1 < (970390452 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 1 = (-23910158 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 1 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-23910158 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 1 +
      (4451662 / 100000000) * (-96 / 100) ^ 1 +
      (2545398 / 100000000) * (88 / 100) ^ 1 +
      (-4932634 / 100000000) * (95 / 100) ^ 1 +
      (11618157 / 100000000) * (984 / 1000) ^ 1 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 1 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 1 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 1 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 1 : ℚ) ^ 2 / 1) <
      970390452 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 1 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_2 :
    barrierV2 2 ^ 2 / 2 < (160633007 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 2 = (21152432 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 2 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((21152432 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 2 +
      (4451662 / 100000000) * (-96 / 100) ^ 2 +
      (2545398 / 100000000) * (88 / 100) ^ 2 +
      (-4932634 / 100000000) * (95 / 100) ^ 2 +
      (11618157 / 100000000) * (984 / 1000) ^ 2 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 2 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 2 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 2 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 2 : ℚ) ^ 2 / 2) <
      160633007 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 2 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_3 :
    barrierV2 3 ^ 2 / 3 < (66118369 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 3 = (-2885110 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 3 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-2885110 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 3 +
      (4451662 / 100000000) * (-96 / 100) ^ 3 +
      (2545398 / 100000000) * (88 / 100) ^ 3 +
      (-4932634 / 100000000) * (95 / 100) ^ 3 +
      (11618157 / 100000000) * (984 / 1000) ^ 3 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 3 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 3 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 3 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 3 : ℚ) ^ 2 / 3) <
      66118369 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 3 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_4 :
    barrierV2 4 ^ 2 / 4 < (1321985 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 4 = (-11558199 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 4 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-11558199 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 4 +
      (4451662 / 100000000) * (-96 / 100) ^ 4 +
      (2545398 / 100000000) * (88 / 100) ^ 4 +
      (-4932634 / 100000000) * (95 / 100) ^ 4 +
      (11618157 / 100000000) * (984 / 1000) ^ 4 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 4 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 4 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 4 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 4 : ℚ) ^ 2 / 4) <
      1321985 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 4 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_5 :
    barrierV2 5 ^ 2 / 5 < (22281708 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 5 = (6485289 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 5 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((6485289 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 5 +
      (4451662 / 100000000) * (-96 / 100) ^ 5 +
      (2545398 / 100000000) * (88 / 100) ^ 5 +
      (-4932634 / 100000000) * (95 / 100) ^ 5 +
      (11618157 / 100000000) * (984 / 1000) ^ 5 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 5 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 5 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 5 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 5 : ℚ) ^ 2 / 5) <
      22281708 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 5 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_6 :
    barrierV2 6 ^ 2 / 6 < (15772063 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 6 = (1456821 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 6 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((1456821 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 6 +
      (4451662 / 100000000) * (-96 / 100) ^ 6 +
      (2545398 / 100000000) * (88 / 100) ^ 6 +
      (-4932634 / 100000000) * (95 / 100) ^ 6 +
      (11618157 / 100000000) * (984 / 1000) ^ 6 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 6 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 6 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 6 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 6 : ℚ) ^ 2 / 6) <
      15772063 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 6 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_7 :
    barrierV2 7 ^ 2 / 7 < (14164646 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 7 = (-1912176 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 7 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-1912176 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 7 +
      (4451662 / 100000000) * (-96 / 100) ^ 7 +
      (2545398 / 100000000) * (88 / 100) ^ 7 +
      (-4932634 / 100000000) * (95 / 100) ^ 7 +
      (11618157 / 100000000) * (984 / 1000) ^ 7 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 7 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 7 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 7 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 7 : ℚ) ^ 2 / 7) <
      14164646 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 7 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_8 :
    barrierV2 8 ^ 2 / 8 < (18955 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 8 = (-2263524 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 8 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-2263524 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 8 +
      (4451662 / 100000000) * (-96 / 100) ^ 8 +
      (2545398 / 100000000) * (88 / 100) ^ 8 +
      (-4932634 / 100000000) * (95 / 100) ^ 8 +
      (11618157 / 100000000) * (984 / 1000) ^ 8 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 8 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 8 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 8 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 8 : ℚ) ^ 2 / 8) <
      18955 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 8 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_8 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (0 + k + 1) ^ 2 / ((0 + k + 1 : ℕ) : ℝ)) ≤
      (1250701185 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_1.le) barrierV2_norm_term_2.le) barrierV2_norm_term_3.le) barrierV2_norm_term_4.le) barrierV2_norm_term_5.le) barrierV2_norm_term_6.le) barrierV2_norm_term_7.le) barrierV2_norm_term_8.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_8 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1250701185 / 1000000000 : ℝ) := by
  simpa only [Nat.zero_add] using barrierV2_norm_block_8

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_9 :
    barrierV2 9 ^ 2 / 9 < (5065162 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 9 = (2742210 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 9 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((2742210 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 9 +
      (4451662 / 100000000) * (-96 / 100) ^ 9 +
      (2545398 / 100000000) * (88 / 100) ^ 9 +
      (-4932634 / 100000000) * (95 / 100) ^ 9 +
      (11618157 / 100000000) * (984 / 1000) ^ 9 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 9 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 9 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 9 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 9 : ℚ) ^ 2 / 9) <
      5065162 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 9 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_10 :
    barrierV2 10 ^ 2 / 10 < (4930284 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 10 = (-1162454 / 100000000 : ℝ) := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 10 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((-1162454 / 100000000) +
      (15199211 / 100000000) * (-8 / 10) ^ 10 +
      (4451662 / 100000000) * (-96 / 100) ^ 10 +
      (2545398 / 100000000) * (88 / 100) ^ 10 +
      (-4932634 / 100000000) * (95 / 100) ^ 10 +
      (11618157 / 100000000) * (984 / 1000) ^ 10 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 10 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 10 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 10 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 10 : ℚ) ^ 2 / 10) <
      4930284 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 10 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_11 :
    barrierV2 11 ^ 2 / 11 < (6326889 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 11 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 11 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 11 +
      (4451662 / 100000000) * (-96 / 100) ^ 11 +
      (2545398 / 100000000) * (88 / 100) ^ 11 +
      (-4932634 / 100000000) * (95 / 100) ^ 11 +
      (11618157 / 100000000) * (984 / 1000) ^ 11 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 11 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 11 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 11 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 11 : ℚ) ^ 2 / 11) <
      6326889 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 11 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_12 :
    barrierV2 12 ^ 2 / 12 < (21348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 12 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 12 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 12 +
      (4451662 / 100000000) * (-96 / 100) ^ 12 +
      (2545398 / 100000000) * (88 / 100) ^ 12 +
      (-4932634 / 100000000) * (95 / 100) ^ 12 +
      (11618157 / 100000000) * (984 / 1000) ^ 12 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 12 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 12 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 12 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 12 : ℚ) ^ 2 / 12) <
      21348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 12 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_13 :
    barrierV2 13 ^ 2 / 13 < (2053383 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 13 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 13 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 13 +
      (4451662 / 100000000) * (-96 / 100) ^ 13 +
      (2545398 / 100000000) * (88 / 100) ^ 13 +
      (-4932634 / 100000000) * (95 / 100) ^ 13 +
      (11618157 / 100000000) * (984 / 1000) ^ 13 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 13 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 13 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 13 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 13 : ℚ) ^ 2 / 13) <
      2053383 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 13 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_14 :
    barrierV2 14 ^ 2 / 14 < (2490942 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 14 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 14 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 14 +
      (4451662 / 100000000) * (-96 / 100) ^ 14 +
      (2545398 / 100000000) * (88 / 100) ^ 14 +
      (-4932634 / 100000000) * (95 / 100) ^ 14 +
      (11618157 / 100000000) * (984 / 1000) ^ 14 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 14 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 14 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 14 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 14 : ℚ) ^ 2 / 14) <
      2490942 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 14 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_15 :
    barrierV2 15 ^ 2 / 15 < (3369446 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 15 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 15 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 15 +
      (4451662 / 100000000) * (-96 / 100) ^ 15 +
      (2545398 / 100000000) * (88 / 100) ^ 15 +
      (-4932634 / 100000000) * (95 / 100) ^ 15 +
      (11618157 / 100000000) * (984 / 1000) ^ 15 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 15 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 15 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 15 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 15 : ℚ) ^ 2 / 15) <
      3369446 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 15 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_16 :
    barrierV2 16 ^ 2 / 16 < (54967 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 16 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 16 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 16 +
      (4451662 / 100000000) * (-96 / 100) ^ 16 +
      (2545398 / 100000000) * (88 / 100) ^ 16 +
      (-4932634 / 100000000) * (95 / 100) ^ 16 +
      (11618157 / 100000000) * (984 / 1000) ^ 16 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 16 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 16 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 16 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 16 : ℚ) ^ 2 / 16) <
      54967 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 16 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_16 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (8 + k + 1) ^ 2 / ((8 + k + 1 : ℕ) : ℝ)) ≤
      (24312421 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_9.le) barrierV2_norm_term_10.le) barrierV2_norm_term_11.le) barrierV2_norm_term_12.le) barrierV2_norm_term_13.le) barrierV2_norm_term_14.le) barrierV2_norm_term_15.le) barrierV2_norm_term_16.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_16 :
    (∑ k ∈ Finset.range 16,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1275013606 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (8 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_8 barrierV2_norm_block_16
  have hc : (1250701185 / 1000000000 : ℝ) + 24312421 / 1000000000 =
      1275013606 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_17 :
    barrierV2 17 ^ 2 / 17 < (870796 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 17 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 17 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 17 +
      (4451662 / 100000000) * (-96 / 100) ^ 17 +
      (2545398 / 100000000) * (88 / 100) ^ 17 +
      (-4932634 / 100000000) * (95 / 100) ^ 17 +
      (11618157 / 100000000) * (984 / 1000) ^ 17 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 17 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 17 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 17 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 17 : ℚ) ^ 2 / 17) <
      870796 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 17 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_18 :
    barrierV2 18 ^ 2 / 18 < (1279000 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 18 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 18 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 18 +
      (4451662 / 100000000) * (-96 / 100) ^ 18 +
      (2545398 / 100000000) * (88 / 100) ^ 18 +
      (-4932634 / 100000000) * (95 / 100) ^ 18 +
      (11618157 / 100000000) * (984 / 1000) ^ 18 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 18 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 18 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 18 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 18 : ℚ) ^ 2 / 18) <
      1279000 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 18 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_19 :
    barrierV2 19 ^ 2 / 19 < (2122938 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 19 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 19 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 19 +
      (4451662 / 100000000) * (-96 / 100) ^ 19 +
      (2545398 / 100000000) * (88 / 100) ^ 19 +
      (-4932634 / 100000000) * (95 / 100) ^ 19 +
      (11618157 / 100000000) * (984 / 1000) ^ 19 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 19 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 19 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 19 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 19 : ℚ) ^ 2 / 19) <
      2122938 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 19 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_20 :
    barrierV2 20 ^ 2 / 20 < (87741 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 20 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 20 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 20 +
      (4451662 / 100000000) * (-96 / 100) ^ 20 +
      (2545398 / 100000000) * (88 / 100) ^ 20 +
      (-4932634 / 100000000) * (95 / 100) ^ 20 +
      (11618157 / 100000000) * (984 / 1000) ^ 20 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 20 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 20 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 20 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 20 : ℚ) ^ 2 / 20) <
      87741 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 20 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_21 :
    barrierV2 21 ^ 2 / 21 < (449313 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 21 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 21 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 21 +
      (4451662 / 100000000) * (-96 / 100) ^ 21 +
      (2545398 / 100000000) * (88 / 100) ^ 21 +
      (-4932634 / 100000000) * (95 / 100) ^ 21 +
      (11618157 / 100000000) * (984 / 1000) ^ 21 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 21 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 21 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 21 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 21 : ℚ) ^ 2 / 21) <
      449313 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 21 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_22 :
    barrierV2 22 ^ 2 / 22 < (720581 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 22 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 22 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 22 +
      (4451662 / 100000000) * (-96 / 100) ^ 22 +
      (2545398 / 100000000) * (88 / 100) ^ 22 +
      (-4932634 / 100000000) * (95 / 100) ^ 22 +
      (11618157 / 100000000) * (984 / 1000) ^ 22 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 22 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 22 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 22 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 22 : ℚ) ^ 2 / 22) <
      720581 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 22 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_23 :
    barrierV2 23 ^ 2 / 23 < (1481876 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 23 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 23 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 23 +
      (4451662 / 100000000) * (-96 / 100) ^ 23 +
      (2545398 / 100000000) * (88 / 100) ^ 23 +
      (-4932634 / 100000000) * (95 / 100) ^ 23 +
      (11618157 / 100000000) * (984 / 1000) ^ 23 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 23 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 23 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 23 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 23 : ℚ) ^ 2 / 23) <
      1481876 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 23 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_24 :
    barrierV2 24 ^ 2 / 24 < (106633 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 24 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 24 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 24 +
      (4451662 / 100000000) * (-96 / 100) ^ 24 +
      (2545398 / 100000000) * (88 / 100) ^ 24 +
      (-4932634 / 100000000) * (95 / 100) ^ 24 +
      (11618157 / 100000000) * (984 / 1000) ^ 24 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 24 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 24 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 24 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 24 : ℚ) ^ 2 / 24) <
      106633 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 24 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_24 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (16 + k + 1) ^ 2 / ((16 + k + 1 : ℕ) : ℝ)) ≤
      (7118878 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_17.le) barrierV2_norm_term_18.le) barrierV2_norm_term_19.le) barrierV2_norm_term_20.le) barrierV2_norm_term_21.le) barrierV2_norm_term_22.le) barrierV2_norm_term_23.le) barrierV2_norm_term_24.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_24 :
    (∑ k ∈ Finset.range 24,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1282132484 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (16 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_16 barrierV2_norm_block_24
  have hc : (1275013606 / 1000000000 : ℝ) + 7118878 / 1000000000 =
      1282132484 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_25 :
    barrierV2 25 ^ 2 / 25 < (265648 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 25 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 25 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 25 +
      (4451662 / 100000000) * (-96 / 100) ^ 25 +
      (2545398 / 100000000) * (88 / 100) ^ 25 +
      (-4932634 / 100000000) * (95 / 100) ^ 25 +
      (11618157 / 100000000) * (984 / 1000) ^ 25 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 25 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 25 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 25 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 25 : ℚ) ^ 2 / 25) <
      265648 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 25 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_26 :
    barrierV2 26 ^ 2 / 26 < (437835 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 26 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 26 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 26 +
      (4451662 / 100000000) * (-96 / 100) ^ 26 +
      (2545398 / 100000000) * (88 / 100) ^ 26 +
      (-4932634 / 100000000) * (95 / 100) ^ 26 +
      (11618157 / 100000000) * (984 / 1000) ^ 26 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 26 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 26 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 26 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 26 : ℚ) ^ 2 / 26) <
      437835 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 26 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_27 :
    barrierV2 27 ^ 2 / 27 < (1103608 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 27 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 27 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 27 +
      (4451662 / 100000000) * (-96 / 100) ^ 27 +
      (2545398 / 100000000) * (88 / 100) ^ 27 +
      (-4932634 / 100000000) * (95 / 100) ^ 27 +
      (11618157 / 100000000) * (984 / 1000) ^ 27 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 27 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 27 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 27 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 27 : ℚ) ^ 2 / 27) <
      1103608 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 27 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_28 :
    barrierV2 28 ^ 2 / 28 < (111715 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 28 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 28 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 28 +
      (4451662 / 100000000) * (-96 / 100) ^ 28 +
      (2545398 / 100000000) * (88 / 100) ^ 28 +
      (-4932634 / 100000000) * (95 / 100) ^ 28 +
      (11618157 / 100000000) * (984 / 1000) ^ 28 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 28 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 28 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 28 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 28 : ℚ) ^ 2 / 28) <
      111715 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 28 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_29 :
    barrierV2 29 ^ 2 / 29 < (172849 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 29 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 29 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 29 +
      (4451662 / 100000000) * (-96 / 100) ^ 29 +
      (2545398 / 100000000) * (88 / 100) ^ 29 +
      (-4932634 / 100000000) * (95 / 100) ^ 29 +
      (11618157 / 100000000) * (984 / 1000) ^ 29 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 29 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 29 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 29 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 29 : ℚ) ^ 2 / 29) <
      172849 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 29 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_30 :
    barrierV2 30 ^ 2 / 30 < (282884 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 30 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 30 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 30 +
      (4451662 / 100000000) * (-96 / 100) ^ 30 +
      (2545398 / 100000000) * (88 / 100) ^ 30 +
      (-4932634 / 100000000) * (95 / 100) ^ 30 +
      (11618157 / 100000000) * (984 / 1000) ^ 30 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 30 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 30 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 30 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 30 : ℚ) ^ 2 / 30) <
      282884 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 30 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_31 :
    barrierV2 31 ^ 2 / 31 < (857115 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 31 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 31 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 31 +
      (4451662 / 100000000) * (-96 / 100) ^ 31 +
      (2545398 / 100000000) * (88 / 100) ^ 31 +
      (-4932634 / 100000000) * (95 / 100) ^ 31 +
      (11618157 / 100000000) * (984 / 1000) ^ 31 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 31 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 31 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 31 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 31 : ℚ) ^ 2 / 31) <
      857115 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 31 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_32 :
    barrierV2 32 ^ 2 / 32 < (107492 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 32 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 32 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 32 +
      (4451662 / 100000000) * (-96 / 100) ^ 32 +
      (2545398 / 100000000) * (88 / 100) ^ 32 +
      (-4932634 / 100000000) * (95 / 100) ^ 32 +
      (11618157 / 100000000) * (984 / 1000) ^ 32 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 32 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 32 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 32 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 32 : ℚ) ^ 2 / 32) <
      107492 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 32 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_32 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (24 + k + 1) ^ 2 / ((24 + k + 1 : ℕ) : ℝ)) ≤
      (3339146 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_25.le) barrierV2_norm_term_26.le) barrierV2_norm_term_27.le) barrierV2_norm_term_28.le) barrierV2_norm_term_29.le) barrierV2_norm_term_30.le) barrierV2_norm_term_31.le) barrierV2_norm_term_32.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_32 :
    (∑ k ∈ Finset.range 32,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1285471630 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (24 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_24 barrierV2_norm_block_32
  have hc : (1282132484 / 1000000000 : ℝ) + 3339146 / 1000000000 =
      1285471630 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_33 :
    barrierV2 33 ^ 2 / 33 < (120428 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 33 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 33 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 33 +
      (4451662 / 100000000) * (-96 / 100) ^ 33 +
      (2545398 / 100000000) * (88 / 100) ^ 33 +
      (-4932634 / 100000000) * (95 / 100) ^ 33 +
      (11618157 / 100000000) * (984 / 1000) ^ 33 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 33 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 33 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 33 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 33 : ℚ) ^ 2 / 33) <
      120428 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 33 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_34 :
    barrierV2 34 ^ 2 / 34 < (192033 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 34 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 34 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 34 +
      (4451662 / 100000000) * (-96 / 100) ^ 34 +
      (2545398 / 100000000) * (88 / 100) ^ 34 +
      (-4932634 / 100000000) * (95 / 100) ^ 34 +
      (11618157 / 100000000) * (984 / 1000) ^ 34 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 34 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 34 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 34 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 34 : ℚ) ^ 2 / 34) <
      192033 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 34 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_35 :
    barrierV2 35 ^ 2 / 35 < (684331 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 35 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 35 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 35 +
      (4451662 / 100000000) * (-96 / 100) ^ 35 +
      (2545398 / 100000000) * (88 / 100) ^ 35 +
      (-4932634 / 100000000) * (95 / 100) ^ 35 +
      (11618157 / 100000000) * (984 / 1000) ^ 35 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 35 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 35 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 35 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 35 : ℚ) ^ 2 / 35) <
      684331 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 35 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_36 :
    barrierV2 36 ^ 2 / 36 < (98292 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 36 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 36 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 36 +
      (4451662 / 100000000) * (-96 / 100) ^ 36 +
      (2545398 / 100000000) * (88 / 100) ^ 36 +
      (-4932634 / 100000000) * (95 / 100) ^ 36 +
      (11618157 / 100000000) * (984 / 1000) ^ 36 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 36 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 36 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 36 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 36 : ℚ) ^ 2 / 36) <
      98292 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 36 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_37 :
    barrierV2 37 ^ 2 / 37 < (88154 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 37 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 37 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 37 +
      (4451662 / 100000000) * (-96 / 100) ^ 37 +
      (2545398 / 100000000) * (88 / 100) ^ 37 +
      (-4932634 / 100000000) * (95 / 100) ^ 37 +
      (11618157 / 100000000) * (984 / 1000) ^ 37 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 37 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 37 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 37 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 37 : ℚ) ^ 2 / 37) <
      88154 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 37 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_38 :
    barrierV2 38 ^ 2 / 38 < (135606 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 38 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 38 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 38 +
      (4451662 / 100000000) * (-96 / 100) ^ 38 +
      (2545398 / 100000000) * (88 / 100) ^ 38 +
      (-4932634 / 100000000) * (95 / 100) ^ 38 +
      (11618157 / 100000000) * (984 / 1000) ^ 38 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 38 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 38 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 38 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 38 : ℚ) ^ 2 / 38) <
      135606 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 38 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_39 :
    barrierV2 39 ^ 2 / 39 < (556543 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 39 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 39 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 39 +
      (4451662 / 100000000) * (-96 / 100) ^ 39 +
      (2545398 / 100000000) * (88 / 100) ^ 39 +
      (-4932634 / 100000000) * (95 / 100) ^ 39 +
      (11618157 / 100000000) * (984 / 1000) ^ 39 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 39 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 39 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 39 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 39 : ℚ) ^ 2 / 39) <
      556543 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 39 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_40 :
    barrierV2 40 ^ 2 / 40 < (87104 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 40 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 40 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 40 +
      (4451662 / 100000000) * (-96 / 100) ^ 40 +
      (2545398 / 100000000) * (88 / 100) ^ 40 +
      (-4932634 / 100000000) * (95 / 100) ^ 40 +
      (11618157 / 100000000) * (984 / 1000) ^ 40 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 40 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 40 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 40 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 40 : ℚ) ^ 2 / 40) <
      87104 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 40 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_40 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (32 + k + 1) ^ 2 / ((32 + k + 1 : ℕ) : ℝ)) ≤
      (1962491 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_33.le) barrierV2_norm_term_34.le) barrierV2_norm_term_35.le) barrierV2_norm_term_36.le) barrierV2_norm_term_37.le) barrierV2_norm_term_38.le) barrierV2_norm_term_39.le) barrierV2_norm_term_40.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_40 :
    (∑ k ∈ Finset.range 40,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1287434121 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (32 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_32 barrierV2_norm_block_40
  have hc : (1285471630 / 1000000000 : ℝ) + 1962491 / 1000000000 =
      1287434121 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_41 :
    barrierV2 41 ^ 2 / 41 < (66892 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 41 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 41 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 41 +
      (4451662 / 100000000) * (-96 / 100) ^ 41 +
      (2545398 / 100000000) * (88 / 100) ^ 41 +
      (-4932634 / 100000000) * (95 / 100) ^ 41 +
      (11618157 / 100000000) * (984 / 1000) ^ 41 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 41 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 41 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 41 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 41 : ℚ) ^ 2 / 41) <
      66892 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 41 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_42 :
    barrierV2 42 ^ 2 / 42 < (98809 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 42 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 42 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 42 +
      (4451662 / 100000000) * (-96 / 100) ^ 42 +
      (2545398 / 100000000) * (88 / 100) ^ 42 +
      (-4932634 / 100000000) * (95 / 100) ^ 42 +
      (11618157 / 100000000) * (984 / 1000) ^ 42 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 42 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 42 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 42 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 42 : ℚ) ^ 2 / 42) <
      98809 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 42 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_43 :
    barrierV2 43 ^ 2 / 43 < (458279 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 43 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 43 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 43 +
      (4451662 / 100000000) * (-96 / 100) ^ 43 +
      (2545398 / 100000000) * (88 / 100) ^ 43 +
      (-4932634 / 100000000) * (95 / 100) ^ 43 +
      (11618157 / 100000000) * (984 / 1000) ^ 43 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 43 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 43 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 43 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 43 : ℚ) ^ 2 / 43) <
      458279 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 43 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_44 :
    barrierV2 44 ^ 2 / 44 < (75686 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 44 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 44 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 44 +
      (4451662 / 100000000) * (-96 / 100) ^ 44 +
      (2545398 / 100000000) * (88 / 100) ^ 44 +
      (-4932634 / 100000000) * (95 / 100) ^ 44 +
      (11618157 / 100000000) * (984 / 1000) ^ 44 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 44 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 44 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 44 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 44 : ℚ) ^ 2 / 44) <
      75686 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 44 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_45 :
    barrierV2 45 ^ 2 / 45 < (52113 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 45 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 45 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 45 +
      (4451662 / 100000000) * (-96 / 100) ^ 45 +
      (2545398 / 100000000) * (88 / 100) ^ 45 +
      (-4932634 / 100000000) * (95 / 100) ^ 45 +
      (11618157 / 100000000) * (984 / 1000) ^ 45 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 45 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 45 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 45 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 45 : ℚ) ^ 2 / 45) <
      52113 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 45 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_46 :
    barrierV2 46 ^ 2 / 46 < (73815 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 46 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 46 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 46 +
      (4451662 / 100000000) * (-96 / 100) ^ 46 +
      (2545398 / 100000000) * (88 / 100) ^ 46 +
      (-4932634 / 100000000) * (95 / 100) ^ 46 +
      (11618157 / 100000000) * (984 / 1000) ^ 46 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 46 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 46 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 46 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 46 : ℚ) ^ 2 / 46) <
      73815 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 46 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero,
    zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_47 :
    barrierV2 47 ^ 2 / 47 < (380579 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 47 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 47 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 47 +
      (4451662 / 100000000) * (-96 / 100) ^ 47 +
      (2545398 / 100000000) * (88 / 100) ^ 47 +
      (-4932634 / 100000000) * (95 / 100) ^ 47 +
      (11618157 / 100000000) * (984 / 1000) ^ 47 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 47 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 47 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 47 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 47 : ℚ) ^ 2 / 47) <
      380579 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 47 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_48 :
    barrierV2 48 ^ 2 / 48 < (64952 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 48 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 48 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 48 +
      (4451662 / 100000000) * (-96 / 100) ^ 48 +
      (2545398 / 100000000) * (88 / 100) ^ 48 +
      (-4932634 / 100000000) * (95 / 100) ^ 48 +
      (11618157 / 100000000) * (984 / 1000) ^ 48 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 48 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 48 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 48 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 48 : ℚ) ^ 2 / 48) <
      64952 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 48 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_48 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (40 + k + 1) ^ 2 / ((40 + k + 1 : ℕ) : ℝ)) ≤
      (1271125 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_41.le) barrierV2_norm_term_42.le) barrierV2_norm_term_43.le) barrierV2_norm_term_44.le) barrierV2_norm_term_45.le) barrierV2_norm_term_46.le) barrierV2_norm_term_47.le) barrierV2_norm_term_48.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_48 :
    (∑ k ∈ Finset.range 48,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1288705246 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (40 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_40 barrierV2_norm_block_48
  have hc : (1287434121 / 1000000000 : ℝ) + 1271125 / 1000000000 =
      1288705246 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormVPrefix096
namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_49 :
    barrierV2 49 ^ 2 / 49 < (41395 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 49 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 49 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 49 +
      (4451662 / 100000000) * (-96 / 100) ^ 49 +
      (2545398 / 100000000) * (88 / 100) ^ 49 +
      (-4932634 / 100000000) * (95 / 100) ^ 49 +
      (11618157 / 100000000) * (984 / 1000) ^ 49 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 49 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 49 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 49 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 49 : ℚ) ^ 2 / 49) <
      41395 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 49 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_50 :
    barrierV2 50 ^ 2 / 50 < (56252 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 50 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 50 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 50 +
      (4451662 / 100000000) * (-96 / 100) ^ 50 +
      (2545398 / 100000000) * (88 / 100) ^ 50 +
      (-4932634 / 100000000) * (95 / 100) ^ 50 +
      (11618157 / 100000000) * (984 / 1000) ^ 50 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 50 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 50 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 50 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 50 : ℚ) ^ 2 / 50) <
      56252 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 50 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_51 :
    barrierV2 51 ^ 2 / 51 < (317915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 51 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 51 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 51 +
      (4451662 / 100000000) * (-96 / 100) ^ 51 +
      (2545398 / 100000000) * (88 / 100) ^ 51 +
      (-4932634 / 100000000) * (95 / 100) ^ 51 +
      (11618157 / 100000000) * (984 / 1000) ^ 51 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 51 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 51 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 51 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 51 : ℚ) ^ 2 / 51) <
      317915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 51 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_52 :
    barrierV2 52 ^ 2 / 52 < (55307 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 52 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 52 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 52 +
      (4451662 / 100000000) * (-96 / 100) ^ 52 +
      (2545398 / 100000000) * (88 / 100) ^ 52 +
      (-4932634 / 100000000) * (95 / 100) ^ 52 +
      (11618157 / 100000000) * (984 / 1000) ^ 52 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 52 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 52 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 52 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 52 : ℚ) ^ 2 / 52) <
      55307 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 52 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_53 :
    barrierV2 53 ^ 2 / 53 < (33358 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 53 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 53 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 53 +
      (4451662 / 100000000) * (-96 / 100) ^ 53 +
      (2545398 / 100000000) * (88 / 100) ^ 53 +
      (-4932634 / 100000000) * (95 / 100) ^ 53 +
      (11618157 / 100000000) * (984 / 1000) ^ 53 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 53 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 53 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 53 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 53 : ℚ) ^ 2 / 53) <
      33358 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 53 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_54 :
    barrierV2 54 ^ 2 / 54 < (43560 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 54 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 54 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 54 +
      (4451662 / 100000000) * (-96 / 100) ^ 54 +
      (2545398 / 100000000) * (88 / 100) ^ 54 +
      (-4932634 / 100000000) * (95 / 100) ^ 54 +
      (11618157 / 100000000) * (984 / 1000) ^ 54 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 54 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 54 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 54 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 54 : ℚ) ^ 2 / 54) <
      43560 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 54 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_55 :
    barrierV2 55 ^ 2 / 55 < (266670 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 55 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 55 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 55 +
      (4451662 / 100000000) * (-96 / 100) ^ 55 +
      (2545398 / 100000000) * (88 / 100) ^ 55 +
      (-4932634 / 100000000) * (95 / 100) ^ 55 +
      (11618157 / 100000000) * (984 / 1000) ^ 55 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 55 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 55 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 55 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 55 : ℚ) ^ 2 / 55) <
      266670 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 55 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_56 :
    barrierV2 56 ^ 2 / 56 < (46867 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 56 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 56 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 56 +
      (4451662 / 100000000) * (-96 / 100) ^ 56 +
      (2545398 / 100000000) * (88 / 100) ^ 56 +
      (-4932634 / 100000000) * (95 / 100) ^ 56 +
      (11618157 / 100000000) * (984 / 1000) ^ 56 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 56 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 56 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 56 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 56 : ℚ) ^ 2 / 56) <
      46867 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 56 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_56 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (48 + k + 1) ^ 2 / ((48 + k + 1 : ℕ) : ℝ)) ≤
      (861324 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_49.le) barrierV2_norm_term_50.le) barrierV2_norm_term_51.le) barrierV2_norm_term_52.le) barrierV2_norm_term_53.le) barrierV2_norm_term_54.le) barrierV2_norm_term_55.le) barrierV2_norm_term_56.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_56 :
    (∑ k ∈ Finset.range 56,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1289566570 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (48 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_48 barrierV2_norm_block_56
  have hc : (1288705246 / 1000000000 : ℝ) + 861324 / 1000000000 =
      1289566570 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_57 :
    barrierV2 57 ^ 2 / 57 < (27174 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 57 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 57 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 57 +
      (4451662 / 100000000) * (-96 / 100) ^ 57 +
      (2545398 / 100000000) * (88 / 100) ^ 57 +
      (-4932634 / 100000000) * (95 / 100) ^ 57 +
      (11618157 / 100000000) * (984 / 1000) ^ 57 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 57 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 57 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 57 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 57 : ℚ) ^ 2 / 57) <
      27174 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 57 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_58 :
    barrierV2 58 ^ 2 / 58 < (34175 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 58 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 58 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 58 +
      (4451662 / 100000000) * (-96 / 100) ^ 58 +
      (2545398 / 100000000) * (88 / 100) ^ 58 +
      (-4932634 / 100000000) * (95 / 100) ^ 58 +
      (11618157 / 100000000) * (984 / 1000) ^ 58 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 58 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 58 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 58 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 58 : ℚ) ^ 2 / 58) <
      34175 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 58 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_59 :
    barrierV2 59 ^ 2 / 59 < (224355 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 59 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 59 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 59 +
      (4451662 / 100000000) * (-96 / 100) ^ 59 +
      (2545398 / 100000000) * (88 / 100) ^ 59 +
      (-4932634 / 100000000) * (95 / 100) ^ 59 +
      (11618157 / 100000000) * (984 / 1000) ^ 59 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 59 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 59 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 59 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 59 : ℚ) ^ 2 / 59) <
      224355 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 59 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_60 :
    barrierV2 60 ^ 2 / 60 < (39602 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 60 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 60 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 60 +
      (4451662 / 100000000) * (-96 / 100) ^ 60 +
      (2545398 / 100000000) * (88 / 100) ^ 60 +
      (-4932634 / 100000000) * (95 / 100) ^ 60 +
      (11618157 / 100000000) * (984 / 1000) ^ 60 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 60 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 60 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 60 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 60 : ℚ) ^ 2 / 60) <
      39602 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 60 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_61 :
    barrierV2 61 ^ 2 / 61 < (22318 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 61 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 61 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 61 +
      (4451662 / 100000000) * (-96 / 100) ^ 61 +
      (2545398 / 100000000) * (88 / 100) ^ 61 +
      (-4932634 / 100000000) * (95 / 100) ^ 61 +
      (11618157 / 100000000) * (984 / 1000) ^ 61 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 61 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 61 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 61 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 61 : ℚ) ^ 2 / 61) <
      22318 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 61 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_62 :
    barrierV2 62 ^ 2 / 62 < (27101 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 62 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 62 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 62 +
      (4451662 / 100000000) * (-96 / 100) ^ 62 +
      (2545398 / 100000000) * (88 / 100) ^ 62 +
      (-4932634 / 100000000) * (95 / 100) ^ 62 +
      (11618157 / 100000000) * (984 / 1000) ^ 62 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 62 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 62 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 62 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 62 : ℚ) ^ 2 / 62) <
      27101 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 62 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_63 :
    barrierV2 63 ^ 2 / 63 < (189173 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 63 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 63 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 63 +
      (4451662 / 100000000) * (-96 / 100) ^ 63 +
      (2545398 / 100000000) * (88 / 100) ^ 63 +
      (-4932634 / 100000000) * (95 / 100) ^ 63 +
      (11618157 / 100000000) * (984 / 1000) ^ 63 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 63 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 63 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 63 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 63 : ℚ) ^ 2 / 63) <
      189173 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 63 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_64 :
    barrierV2 64 ^ 2 / 64 < (33410 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 64 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 64 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 64 +
      (4451662 / 100000000) * (-96 / 100) ^ 64 +
      (2545398 / 100000000) * (88 / 100) ^ 64 +
      (-4932634 / 100000000) * (95 / 100) ^ 64 +
      (11618157 / 100000000) * (984 / 1000) ^ 64 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 64 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 64 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 64 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 64 : ℚ) ^ 2 / 64) <
      33410 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 64 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_64 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (56 + k + 1) ^ 2 / ((56 + k + 1 : ℕ) : ℝ)) ≤
      (597308 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_57.le) barrierV2_norm_term_58.le) barrierV2_norm_term_59.le) barrierV2_norm_term_60.le) barrierV2_norm_term_61.le) barrierV2_norm_term_62.le) barrierV2_norm_term_63.le) barrierV2_norm_term_64.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_64 :
    (∑ k ∈ Finset.range 64,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290163878 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (56 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_56 barrierV2_norm_block_64
  have hc : (1289566570 / 1000000000 : ℝ) + 597308 / 1000000000 =
      1290163878 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_65 :
    barrierV2 65 ^ 2 / 65 < (18446 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 65 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 65 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 65 +
      (4451662 / 100000000) * (-96 / 100) ^ 65 +
      (2545398 / 100000000) * (88 / 100) ^ 65 +
      (-4932634 / 100000000) * (95 / 100) ^ 65 +
      (11618157 / 100000000) * (984 / 1000) ^ 65 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 65 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 65 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 65 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 65 : ℚ) ^ 2 / 65) <
      18446 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 65 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_66 :
    barrierV2 66 ^ 2 / 66 < (21684 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 66 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 66 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 66 +
      (4451662 / 100000000) * (-96 / 100) ^ 66 +
      (2545398 / 100000000) * (88 / 100) ^ 66 +
      (-4932634 / 100000000) * (95 / 100) ^ 66 +
      (11618157 / 100000000) * (984 / 1000) ^ 66 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 66 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 66 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 66 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 66 : ℚ) ^ 2 / 66) <
      21684 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 66 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_67 :
    barrierV2 67 ^ 2 / 67 < (159780 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 67 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 67 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 67 +
      (4451662 / 100000000) * (-96 / 100) ^ 67 +
      (2545398 / 100000000) * (88 / 100) ^ 67 +
      (-4932634 / 100000000) * (95 / 100) ^ 67 +
      (11618157 / 100000000) * (984 / 1000) ^ 67 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 67 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 67 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 67 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 67 : ℚ) ^ 2 / 67) <
      159780 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 67 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_68 :
    barrierV2 68 ^ 2 / 68 < (28167 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 68 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 68 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 68 +
      (4451662 / 100000000) * (-96 / 100) ^ 68 +
      (2545398 / 100000000) * (88 / 100) ^ 68 +
      (-4932634 / 100000000) * (95 / 100) ^ 68 +
      (11618157 / 100000000) * (984 / 1000) ^ 68 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 68 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 68 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 68 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 68 : ℚ) ^ 2 / 68) <
      28167 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 68 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_69 :
    barrierV2 69 ^ 2 / 69 < (15321 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 69 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 69 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 69 +
      (4451662 / 100000000) * (-96 / 100) ^ 69 +
      (2545398 / 100000000) * (88 / 100) ^ 69 +
      (-4932634 / 100000000) * (95 / 100) ^ 69 +
      (11618157 / 100000000) * (984 / 1000) ^ 69 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 69 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 69 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 69 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 69 : ℚ) ^ 2 / 69) <
      15321 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 69 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_70 :
    barrierV2 70 ^ 2 / 70 < (17482 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 70 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 70 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 70 +
      (4451662 / 100000000) * (-96 / 100) ^ 70 +
      (2545398 / 100000000) * (88 / 100) ^ 70 +
      (-4932634 / 100000000) * (95 / 100) ^ 70 +
      (11618157 / 100000000) * (984 / 1000) ^ 70 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 70 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 70 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 70 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 70 : ℚ) ^ 2 / 70) <
      17482 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 70 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_71 :
    barrierV2 71 ^ 2 / 71 < (135138 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 71 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 71 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 71 +
      (4451662 / 100000000) * (-96 / 100) ^ 71 +
      (2545398 / 100000000) * (88 / 100) ^ 71 +
      (-4932634 / 100000000) * (95 / 100) ^ 71 +
      (11618157 / 100000000) * (984 / 1000) ^ 71 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 71 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 71 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 71 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 71 : ℚ) ^ 2 / 71) <
      135138 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 71 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_72 :
    barrierV2 72 ^ 2 / 72 < (23745 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 72 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 72 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 72 +
      (4451662 / 100000000) * (-96 / 100) ^ 72 +
      (2545398 / 100000000) * (88 / 100) ^ 72 +
      (-4932634 / 100000000) * (95 / 100) ^ 72 +
      (11618157 / 100000000) * (984 / 1000) ^ 72 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 72 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 72 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 72 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 72 : ℚ) ^ 2 / 72) <
      23745 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 72 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_72 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (64 + k + 1) ^ 2 / ((64 + k + 1 : ℕ) : ℝ)) ≤
      (419763 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_65.le) barrierV2_norm_term_66.le) barrierV2_norm_term_67.le) barrierV2_norm_term_68.le) barrierV2_norm_term_69.le) barrierV2_norm_term_70.le) barrierV2_norm_term_71.le) barrierV2_norm_term_72.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_72 :
    (∑ k ∈ Finset.range 72,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290583641 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (64 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_64 barrierV2_norm_block_72
  have hc : (1290163878 / 1000000000 : ℝ) + 419763 / 1000000000 =
      1290583641 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_73 :
    barrierV2 73 ^ 2 / 73 < (12775 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 73 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 73 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 73 +
      (4451662 / 100000000) * (-96 / 100) ^ 73 +
      (2545398 / 100000000) * (88 / 100) ^ 73 +
      (-4932634 / 100000000) * (95 / 100) ^ 73 +
      (11618157 / 100000000) * (984 / 1000) ^ 73 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 73 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 73 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 73 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 73 : ℚ) ^ 2 / 73) <
      12775 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 73 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_74 :
    barrierV2 74 ^ 2 / 74 < (14186 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 74 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 74 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 74 +
      (4451662 / 100000000) * (-96 / 100) ^ 74 +
      (2545398 / 100000000) * (88 / 100) ^ 74 +
      (-4932634 / 100000000) * (95 / 100) ^ 74 +
      (11618157 / 100000000) * (984 / 1000) ^ 74 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 74 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 74 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 74 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 74 : ℚ) ^ 2 / 74) <
      14186 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 74 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_75 :
    barrierV2 75 ^ 2 / 75 < (114425 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 75 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 75 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 75 +
      (4451662 / 100000000) * (-96 / 100) ^ 75 +
      (2545398 / 100000000) * (88 / 100) ^ 75 +
      (-4932634 / 100000000) * (95 / 100) ^ 75 +
      (11618157 / 100000000) * (984 / 1000) ^ 75 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 75 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 75 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 75 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 75 : ℚ) ^ 2 / 75) <
      114425 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 75 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_76 :
    barrierV2 76 ^ 2 / 76 < (20022 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 76 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 76 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 76 +
      (4451662 / 100000000) * (-96 / 100) ^ 76 +
      (2545398 / 100000000) * (88 / 100) ^ 76 +
      (-4932634 / 100000000) * (95 / 100) ^ 76 +
      (11618157 / 100000000) * (984 / 1000) ^ 76 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 76 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 76 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 76 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 76 : ℚ) ^ 2 / 76) <
      20022 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 76 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_77 :
    barrierV2 77 ^ 2 / 77 < (10687 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 77 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 77 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 77 +
      (4451662 / 100000000) * (-96 / 100) ^ 77 +
      (2545398 / 100000000) * (88 / 100) ^ 77 +
      (-4932634 / 100000000) * (95 / 100) ^ 77 +
      (11618157 / 100000000) * (984 / 1000) ^ 77 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 77 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 77 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 77 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 77 : ℚ) ^ 2 / 77) <
      10687 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 77 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_78 :
    barrierV2 78 ^ 2 / 78 < (11577 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 78 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 78 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 78 +
      (4451662 / 100000000) * (-96 / 100) ^ 78 +
      (2545398 / 100000000) * (88 / 100) ^ 78 +
      (-4932634 / 100000000) * (95 / 100) ^ 78 +
      (11618157 / 100000000) * (984 / 1000) ^ 78 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 78 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 78 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 78 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 78 : ℚ) ^ 2 / 78) <
      11577 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 78 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_79 :
    barrierV2 79 ^ 2 / 79 < (96981 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 79 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 79 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 79 +
      (4451662 / 100000000) * (-96 / 100) ^ 79 +
      (2545398 / 100000000) * (88 / 100) ^ 79 +
      (-4932634 / 100000000) * (95 / 100) ^ 79 +
      (11618157 / 100000000) * (984 / 1000) ^ 79 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 79 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 79 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 79 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 79 : ℚ) ^ 2 / 79) <
      96981 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 79 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_80 :
    barrierV2 80 ^ 2 / 80 < (16892 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 80 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 80 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 80 +
      (4451662 / 100000000) * (-96 / 100) ^ 80 +
      (2545398 / 100000000) * (88 / 100) ^ 80 +
      (-4932634 / 100000000) * (95 / 100) ^ 80 +
      (11618157 / 100000000) * (984 / 1000) ^ 80 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 80 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 80 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 80 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 80 : ℚ) ^ 2 / 80) <
      16892 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 80 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_80 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (72 + k + 1) ^ 2 / ((72 + k + 1 : ℕ) : ℝ)) ≤
      (297545 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_73.le) barrierV2_norm_term_74.le) barrierV2_norm_term_75.le) barrierV2_norm_term_76.le) barrierV2_norm_term_77.le) barrierV2_norm_term_78.le) barrierV2_norm_term_79.le) barrierV2_norm_term_80.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_80 :
    (∑ k ∈ Finset.range 80,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1290881186 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (72 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_72 barrierV2_norm_block_80
  have hc : (1290583641 / 1000000000 : ℝ) + 297545 / 1000000000 =
      1290881186 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_81 :
    barrierV2 81 ^ 2 / 81 < (8964 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 81 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 81 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 81 +
      (4451662 / 100000000) * (-96 / 100) ^ 81 +
      (2545398 / 100000000) * (88 / 100) ^ 81 +
      (-4932634 / 100000000) * (95 / 100) ^ 81 +
      (11618157 / 100000000) * (984 / 1000) ^ 81 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 81 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 81 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 81 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 81 : ℚ) ^ 2 / 81) <
      8964 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 81 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_82 :
    barrierV2 82 ^ 2 / 82 < (9494 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 82 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 82 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 82 +
      (4451662 / 100000000) * (-96 / 100) ^ 82 +
      (2545398 / 100000000) * (88 / 100) ^ 82 +
      (-4932634 / 100000000) * (95 / 100) ^ 82 +
      (11618157 / 100000000) * (984 / 1000) ^ 82 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 82 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 82 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 82 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 82 : ℚ) ^ 2 / 82) <
      9494 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 82 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_83 :
    barrierV2 83 ^ 2 / 83 < (82268 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 83 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 83 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 83 +
      (4451662 / 100000000) * (-96 / 100) ^ 83 +
      (2545398 / 100000000) * (88 / 100) ^ 83 +
      (-4932634 / 100000000) * (95 / 100) ^ 83 +
      (11618157 / 100000000) * (984 / 1000) ^ 83 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 83 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 83 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 83 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 83 : ℚ) ^ 2 / 83) <
      82268 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 83 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_84 :
    barrierV2 84 ^ 2 / 84 < (14261 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 84 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 84 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 84 +
      (4451662 / 100000000) * (-96 / 100) ^ 84 +
      (2545398 / 100000000) * (88 / 100) ^ 84 +
      (-4932634 / 100000000) * (95 / 100) ^ 84 +
      (11618157 / 100000000) * (984 / 1000) ^ 84 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 84 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 84 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 84 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 84 : ℚ) ^ 2 / 84) <
      14261 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 84 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_85 :
    barrierV2 85 ^ 2 / 85 < (7536 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 85 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 85 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 85 +
      (4451662 / 100000000) * (-96 / 100) ^ 85 +
      (2545398 / 100000000) * (88 / 100) ^ 85 +
      (-4932634 / 100000000) * (95 / 100) ^ 85 +
      (11618157 / 100000000) * (984 / 1000) ^ 85 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 85 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 85 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 85 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 85 : ℚ) ^ 2 / 85) <
      7536 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 85 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_86 :
    barrierV2 86 ^ 2 / 86 < (7820 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 86 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 86 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 86 +
      (4451662 / 100000000) * (-96 / 100) ^ 86 +
      (2545398 / 100000000) * (88 / 100) ^ 86 +
      (-4932634 / 100000000) * (95 / 100) ^ 86 +
      (11618157 / 100000000) * (984 / 1000) ^ 86 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 86 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 86 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 86 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 86 : ℚ) ^ 2 / 86) <
      7820 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 86 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_87 :
    barrierV2 87 ^ 2 / 87 < (69843 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 87 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 87 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 87 +
      (4451662 / 100000000) * (-96 / 100) ^ 87 +
      (2545398 / 100000000) * (88 / 100) ^ 87 +
      (-4932634 / 100000000) * (95 / 100) ^ 87 +
      (11618157 / 100000000) * (984 / 1000) ^ 87 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 87 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 87 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 87 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 87 : ℚ) ^ 2 / 87) <
      69843 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 87 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_88 :
    barrierV2 88 ^ 2 / 88 < (12050 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 88 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 88 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 88 +
      (4451662 / 100000000) * (-96 / 100) ^ 88 +
      (2545398 / 100000000) * (88 / 100) ^ 88 +
      (-4932634 / 100000000) * (95 / 100) ^ 88 +
      (11618157 / 100000000) * (984 / 1000) ^ 88 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 88 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 88 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 88 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 88 : ℚ) ^ 2 / 88) <
      12050 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 88 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_88 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (80 + k + 1) ^ 2 / ((80 + k + 1 : ℕ) : ℝ)) ≤
      (212236 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_81.le) barrierV2_norm_term_82.le) barrierV2_norm_term_83.le) barrierV2_norm_term_84.le) barrierV2_norm_term_85.le) barrierV2_norm_term_86.le) barrierV2_norm_term_87.le) barrierV2_norm_term_88.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_88 :
    (∑ k ∈ Finset.range 88,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291093422 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (80 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_80 barrierV2_norm_block_88
  have hc : (1290881186 / 1000000000 : ℝ) + 212236 / 1000000000 =
      1291093422 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_89 :
    barrierV2 89 ^ 2 / 89 < (6348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 89 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 89 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 89 +
      (4451662 / 100000000) * (-96 / 100) ^ 89 +
      (2545398 / 100000000) * (88 / 100) ^ 89 +
      (-4932634 / 100000000) * (95 / 100) ^ 89 +
      (11618157 / 100000000) * (984 / 1000) ^ 89 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 89 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 89 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 89 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 89 : ℚ) ^ 2 / 89) <
      6348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 89 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_90 :
    barrierV2 90 ^ 2 / 90 < (6466 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 90 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 90 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 90 +
      (4451662 / 100000000) * (-96 / 100) ^ 90 +
      (2545398 / 100000000) * (88 / 100) ^ 90 +
      (-4932634 / 100000000) * (95 / 100) ^ 90 +
      (11618157 / 100000000) * (984 / 1000) ^ 90 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 90 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 90 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 90 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 90 : ℚ) ^ 2 / 90) <
      6466 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 90 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_91 :
    barrierV2 91 ^ 2 / 91 < (59338 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 91 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 91 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 91 +
      (4451662 / 100000000) * (-96 / 100) ^ 91 +
      (2545398 / 100000000) * (88 / 100) ^ 91 +
      (-4932634 / 100000000) * (95 / 100) ^ 91 +
      (11618157 / 100000000) * (984 / 1000) ^ 91 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 91 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 91 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 91 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 91 : ℚ) ^ 2 / 91) <
      59338 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 91 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_92 :
    barrierV2 92 ^ 2 / 92 < (10190 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 92 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 92 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 92 +
      (4451662 / 100000000) * (-96 / 100) ^ 92 +
      (2545398 / 100000000) * (88 / 100) ^ 92 +
      (-4932634 / 100000000) * (95 / 100) ^ 92 +
      (11618157 / 100000000) * (984 / 1000) ^ 92 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 92 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 92 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 92 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 92 : ℚ) ^ 2 / 92) <
      10190 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 92 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_93 :
    barrierV2 93 ^ 2 / 93 < (5357 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 93 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 93 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 93 +
      (4451662 / 100000000) * (-96 / 100) ^ 93 +
      (2545398 / 100000000) * (88 / 100) ^ 93 +
      (-4932634 / 100000000) * (95 / 100) ^ 93 +
      (11618157 / 100000000) * (984 / 1000) ^ 93 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 93 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 93 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 93 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 93 : ℚ) ^ 2 / 93) <
      5357 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 93 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_94 :
    barrierV2 94 ^ 2 / 94 < (5365 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 94 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 94 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 94 +
      (4451662 / 100000000) * (-96 / 100) ^ 94 +
      (2545398 / 100000000) * (88 / 100) ^ 94 +
      (-4932634 / 100000000) * (95 / 100) ^ 94 +
      (11618157 / 100000000) * (984 / 1000) ^ 94 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 94 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 94 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 94 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 94 : ℚ) ^ 2 / 94) <
      5365 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 94 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_95 :
    barrierV2 95 ^ 2 / 95 < (50450 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 95 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 95 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 95 +
      (4451662 / 100000000) * (-96 / 100) ^ 95 +
      (2545398 / 100000000) * (88 / 100) ^ 95 +
      (-4932634 / 100000000) * (95 / 100) ^ 95 +
      (11618157 / 100000000) * (984 / 1000) ^ 95 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 95 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 95 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 95 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 95 : ℚ) ^ 2 / 95) <
      50450 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 95 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_96 :
    barrierV2 96 ^ 2 / 96 < (8626 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 96 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 96 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 96 +
      (4451662 / 100000000) * (-96 / 100) ^ 96 +
      (2545398 / 100000000) * (88 / 100) ^ 96 +
      (-4932634 / 100000000) * (95 / 100) ^ 96 +
      (11618157 / 100000000) * (984 / 1000) ^ 96 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 96 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 96 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 96 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 96 : ℚ) ^ 2 / 96) <
      8626 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 96 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_96 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (88 + k + 1) ^ 2 / ((88 + k + 1 : ℕ) : ℝ)) ≤
      (152140 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_89.le) barrierV2_norm_term_90.le) barrierV2_norm_term_91.le) barrierV2_norm_term_92.le) barrierV2_norm_term_93.le) barrierV2_norm_term_94.le) barrierV2_norm_term_95.le) barrierV2_norm_term_96.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_96 :
    (∑ k ∈ Finset.range 96,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291245562 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (88 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_88 barrierV2_norm_block_96
  have hc : (1291093422 / 1000000000 : ℝ) + 152140 / 1000000000 =
      1291245562 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormVPrefix144
namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_97 :
    barrierV2 97 ^ 2 / 97 < (4527 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 97 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 97 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 97 +
      (4451662 / 100000000) * (-96 / 100) ^ 97 +
      (2545398 / 100000000) * (88 / 100) ^ 97 +
      (-4932634 / 100000000) * (95 / 100) ^ 97 +
      (11618157 / 100000000) * (984 / 1000) ^ 97 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 97 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 97 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 97 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 97 : ℚ) ^ 2 / 97) <
      4527 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 97 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_98 :
    barrierV2 98 ^ 2 / 98 < (4466 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 98 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 98 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 98 +
      (4451662 / 100000000) * (-96 / 100) ^ 98 +
      (2545398 / 100000000) * (88 / 100) ^ 98 +
      (-4932634 / 100000000) * (95 / 100) ^ 98 +
      (11618157 / 100000000) * (984 / 1000) ^ 98 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 98 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 98 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 98 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 98 : ℚ) ^ 2 / 98) <
      4466 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 98 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_99 :
    barrierV2 99 ^ 2 / 99 < (42922 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 99 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 99 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 99 +
      (4451662 / 100000000) * (-96 / 100) ^ 99 +
      (2545398 / 100000000) * (88 / 100) ^ 99 +
      (-4932634 / 100000000) * (95 / 100) ^ 99 +
      (11618157 / 100000000) * (984 / 1000) ^ 99 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 99 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 99 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 99 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 99 : ℚ) ^ 2 / 99) <
      42922 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 99 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_100 :
    barrierV2 100 ^ 2 / 100 < (7308 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 100 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 100 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 100 +
      (4451662 / 100000000) * (-96 / 100) ^ 100 +
      (2545398 / 100000000) * (88 / 100) ^ 100 +
      (-4932634 / 100000000) * (95 / 100) ^ 100 +
      (11618157 / 100000000) * (984 / 1000) ^ 100 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 100 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 100 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 100 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 100 : ℚ) ^ 2 / 100) <
      7308 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 100 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_101 :
    barrierV2 101 ^ 2 / 101 < (3831 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 101 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 101 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 101 +
      (4451662 / 100000000) * (-96 / 100) ^ 101 +
      (2545398 / 100000000) * (88 / 100) ^ 101 +
      (-4932634 / 100000000) * (95 / 100) ^ 101 +
      (11618157 / 100000000) * (984 / 1000) ^ 101 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 101 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 101 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 101 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 101 : ℚ) ^ 2 / 101) <
      3831 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 101 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_102 :
    barrierV2 102 ^ 2 / 102 < (3729 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 102 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 102 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 102 +
      (4451662 / 100000000) * (-96 / 100) ^ 102 +
      (2545398 / 100000000) * (88 / 100) ^ 102 +
      (-4932634 / 100000000) * (95 / 100) ^ 102 +
      (11618157 / 100000000) * (984 / 1000) ^ 102 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 102 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 102 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 102 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 102 : ℚ) ^ 2 / 102) <
      3729 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 102 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_103 :
    barrierV2 103 ^ 2 / 103 < (36542 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 103 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 103 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 103 +
      (4451662 / 100000000) * (-96 / 100) ^ 103 +
      (2545398 / 100000000) * (88 / 100) ^ 103 +
      (-4932634 / 100000000) * (95 / 100) ^ 103 +
      (11618157 / 100000000) * (984 / 1000) ^ 103 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 103 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 103 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 103 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 103 : ℚ) ^ 2 / 103) <
      36542 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 103 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_104 :
    barrierV2 104 ^ 2 / 104 < (6197 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 104 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 104 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 104 +
      (4451662 / 100000000) * (-96 / 100) ^ 104 +
      (2545398 / 100000000) * (88 / 100) ^ 104 +
      (-4932634 / 100000000) * (95 / 100) ^ 104 +
      (11618157 / 100000000) * (984 / 1000) ^ 104 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 104 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 104 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 104 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 104 : ℚ) ^ 2 / 104) <
      6197 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 104 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_104 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (96 + k + 1) ^ 2 / ((96 + k + 1 : ℕ) : ℝ)) ≤
      (109522 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_97.le) barrierV2_norm_term_98.le) barrierV2_norm_term_99.le) barrierV2_norm_term_100.le) barrierV2_norm_term_101.le) barrierV2_norm_term_102.le) barrierV2_norm_term_103.le) barrierV2_norm_term_104.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_104 :
    (∑ k ∈ Finset.range 104,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291355084 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (96 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_96 barrierV2_norm_block_104
  have hc : (1291245562 / 1000000000 : ℝ) + 109522 / 1000000000 =
      1291355084 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_105 :
    barrierV2 105 ^ 2 / 105 < (3246 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 105 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 105 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 105 +
      (4451662 / 100000000) * (-96 / 100) ^ 105 +
      (2545398 / 100000000) * (88 / 100) ^ 105 +
      (-4932634 / 100000000) * (95 / 100) ^ 105 +
      (11618157 / 100000000) * (984 / 1000) ^ 105 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 105 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 105 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 105 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 105 : ℚ) ^ 2 / 105) <
      3246 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 105 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_106 :
    barrierV2 106 ^ 2 / 106 < (3121 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 106 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 106 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 106 +
      (4451662 / 100000000) * (-96 / 100) ^ 106 +
      (2545398 / 100000000) * (88 / 100) ^ 106 +
      (-4932634 / 100000000) * (95 / 100) ^ 106 +
      (11618157 / 100000000) * (984 / 1000) ^ 106 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 106 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 106 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 106 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 106 : ℚ) ^ 2 / 106) <
      3121 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 106 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_107 :
    barrierV2 107 ^ 2 / 107 < (31130 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 107 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 107 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 107 +
      (4451662 / 100000000) * (-96 / 100) ^ 107 +
      (2545398 / 100000000) * (88 / 100) ^ 107 +
      (-4932634 / 100000000) * (95 / 100) ^ 107 +
      (11618157 / 100000000) * (984 / 1000) ^ 107 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 107 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 107 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 107 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 107 : ℚ) ^ 2 / 107) <
      31130 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 107 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_108 :
    barrierV2 108 ^ 2 / 108 < (5260 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 108 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 108 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 108 +
      (4451662 / 100000000) * (-96 / 100) ^ 108 +
      (2545398 / 100000000) * (88 / 100) ^ 108 +
      (-4932634 / 100000000) * (95 / 100) ^ 108 +
      (11618157 / 100000000) * (984 / 1000) ^ 108 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 108 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 108 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 108 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 108 : ℚ) ^ 2 / 108) <
      5260 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 108 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_109 :
    barrierV2 109 ^ 2 / 109 < (2754 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 109 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 109 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 109 +
      (4451662 / 100000000) * (-96 / 100) ^ 109 +
      (2545398 / 100000000) * (88 / 100) ^ 109 +
      (-4932634 / 100000000) * (95 / 100) ^ 109 +
      (11618157 / 100000000) * (984 / 1000) ^ 109 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 109 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 109 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 109 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 109 : ℚ) ^ 2 / 109) <
      2754 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 109 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_110 :
    barrierV2 110 ^ 2 / 110 < (2619 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 110 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 110 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 110 +
      (4451662 / 100000000) * (-96 / 100) ^ 110 +
      (2545398 / 100000000) * (88 / 100) ^ 110 +
      (-4932634 / 100000000) * (95 / 100) ^ 110 +
      (11618157 / 100000000) * (984 / 1000) ^ 110 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 110 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 110 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 110 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 110 : ℚ) ^ 2 / 110) <
      2619 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 110 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_111 :
    barrierV2 111 ^ 2 / 111 < (26537 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 111 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 111 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 111 +
      (4451662 / 100000000) * (-96 / 100) ^ 111 +
      (2545398 / 100000000) * (88 / 100) ^ 111 +
      (-4932634 / 100000000) * (95 / 100) ^ 111 +
      (11618157 / 100000000) * (984 / 1000) ^ 111 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 111 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 111 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 111 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 111 : ℚ) ^ 2 / 111) <
      26537 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 111 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_112 :
    barrierV2 112 ^ 2 / 112 < (4469 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 112 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 112 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 112 +
      (4451662 / 100000000) * (-96 / 100) ^ 112 +
      (2545398 / 100000000) * (88 / 100) ^ 112 +
      (-4932634 / 100000000) * (95 / 100) ^ 112 +
      (11618157 / 100000000) * (984 / 1000) ^ 112 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 112 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 112 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 112 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 112 : ℚ) ^ 2 / 112) <
      4469 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 112 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_112 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (104 + k + 1) ^ 2 / ((104 + k + 1 : ℕ) : ℝ)) ≤
      (79136 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_105.le) barrierV2_norm_term_106.le) barrierV2_norm_term_107.le) barrierV2_norm_term_108.le) barrierV2_norm_term_109.le) barrierV2_norm_term_110.le) barrierV2_norm_term_111.le) barrierV2_norm_term_112.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_112 :
    (∑ k ∈ Finset.range 112,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291434220 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (104 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_104 barrierV2_norm_block_112
  have hc : (1291355084 / 1000000000 : ℝ) + 79136 / 1000000000 =
      1291434220 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_113 :
    barrierV2 113 ^ 2 / 113 < (2339 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 113 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 113 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 113 +
      (4451662 / 100000000) * (-96 / 100) ^ 113 +
      (2545398 / 100000000) * (88 / 100) ^ 113 +
      (-4932634 / 100000000) * (95 / 100) ^ 113 +
      (11618157 / 100000000) * (984 / 1000) ^ 113 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 113 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 113 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 113 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 113 : ℚ) ^ 2 / 113) <
      2339 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 113 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_114 :
    barrierV2 114 ^ 2 / 114 < (2202 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 114 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 114 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 114 +
      (4451662 / 100000000) * (-96 / 100) ^ 114 +
      (2545398 / 100000000) * (88 / 100) ^ 114 +
      (-4932634 / 100000000) * (95 / 100) ^ 114 +
      (11618157 / 100000000) * (984 / 1000) ^ 114 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 114 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 114 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 114 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 114 : ℚ) ^ 2 / 114) <
      2202 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 114 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_115 :
    barrierV2 115 ^ 2 / 115 < (22636 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 115 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 115 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 115 +
      (4451662 / 100000000) * (-96 / 100) ^ 115 +
      (2545398 / 100000000) * (88 / 100) ^ 115 +
      (-4932634 / 100000000) * (95 / 100) ^ 115 +
      (11618157 / 100000000) * (984 / 1000) ^ 115 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 115 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 115 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 115 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 115 : ℚ) ^ 2 / 115) <
      22636 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 115 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_116 :
    barrierV2 116 ^ 2 / 116 < (3800 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 116 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 116 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 116 +
      (4451662 / 100000000) * (-96 / 100) ^ 116 +
      (2545398 / 100000000) * (88 / 100) ^ 116 +
      (-4932634 / 100000000) * (95 / 100) ^ 116 +
      (11618157 / 100000000) * (984 / 1000) ^ 116 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 116 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 116 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 116 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 116 : ℚ) ^ 2 / 116) <
      3800 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 116 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_117 :
    barrierV2 117 ^ 2 / 117 < (1989 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 117 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 117 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 117 +
      (4451662 / 100000000) * (-96 / 100) ^ 117 +
      (2545398 / 100000000) * (88 / 100) ^ 117 +
      (-4932634 / 100000000) * (95 / 100) ^ 117 +
      (11618157 / 100000000) * (984 / 1000) ^ 117 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 117 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 117 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 117 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 117 : ℚ) ^ 2 / 117) <
      1989 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 117 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_118 :
    barrierV2 118 ^ 2 / 118 < (1855 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 118 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 118 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 118 +
      (4451662 / 100000000) * (-96 / 100) ^ 118 +
      (2545398 / 100000000) * (88 / 100) ^ 118 +
      (-4932634 / 100000000) * (95 / 100) ^ 118 +
      (11618157 / 100000000) * (984 / 1000) ^ 118 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 118 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 118 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 118 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 118 : ℚ) ^ 2 / 118) <
      1855 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 118 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_119 :
    barrierV2 119 ^ 2 / 119 < (19320 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 119 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 119 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 119 +
      (4451662 / 100000000) * (-96 / 100) ^ 119 +
      (2545398 / 100000000) * (88 / 100) ^ 119 +
      (-4932634 / 100000000) * (95 / 100) ^ 119 +
      (11618157 / 100000000) * (984 / 1000) ^ 119 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 119 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 119 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 119 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 119 : ℚ) ^ 2 / 119) <
      19320 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 119 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_120 :
    barrierV2 120 ^ 2 / 120 < (3234 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 120 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 120 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 120 +
      (4451662 / 100000000) * (-96 / 100) ^ 120 +
      (2545398 / 100000000) * (88 / 100) ^ 120 +
      (-4932634 / 100000000) * (95 / 100) ^ 120 +
      (11618157 / 100000000) * (984 / 1000) ^ 120 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 120 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 120 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 120 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 120 : ℚ) ^ 2 / 120) <
      3234 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 120 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_120 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (112 + k + 1) ^ 2 / ((112 + k + 1 : ℕ) : ℝ)) ≤
      (57375 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_113.le) barrierV2_norm_term_114.le) barrierV2_norm_term_115.le) barrierV2_norm_term_116.le) barrierV2_norm_term_117.le) barrierV2_norm_term_118.le) barrierV2_norm_term_119.le) barrierV2_norm_term_120.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_120 :
    (∑ k ∈ Finset.range 120,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291491595 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (112 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_112 barrierV2_norm_block_120
  have hc : (1291434220 / 1000000000 : ℝ) + 57375 / 1000000000 =
      1291491595 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_121 :
    barrierV2 121 ^ 2 / 121 < (1692 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 121 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 121 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 121 +
      (4451662 / 100000000) * (-96 / 100) ^ 121 +
      (2545398 / 100000000) * (88 / 100) ^ 121 +
      (-4932634 / 100000000) * (95 / 100) ^ 121 +
      (11618157 / 100000000) * (984 / 1000) ^ 121 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 121 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 121 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 121 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 121 : ℚ) ^ 2 / 121) <
      1692 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 121 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_122 :
    barrierV2 122 ^ 2 / 122 < (1566 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 122 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 122 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 122 +
      (4451662 / 100000000) * (-96 / 100) ^ 122 +
      (2545398 / 100000000) * (88 / 100) ^ 122 +
      (-4932634 / 100000000) * (95 / 100) ^ 122 +
      (11618157 / 100000000) * (984 / 1000) ^ 122 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 122 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 122 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 122 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 122 : ℚ) ^ 2 / 122) <
      1566 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 122 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_123 :
    barrierV2 123 ^ 2 / 123 < (16499 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 123 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 123 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 123 +
      (4451662 / 100000000) * (-96 / 100) ^ 123 +
      (2545398 / 100000000) * (88 / 100) ^ 123 +
      (-4932634 / 100000000) * (95 / 100) ^ 123 +
      (11618157 / 100000000) * (984 / 1000) ^ 123 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 123 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 123 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 123 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 123 : ℚ) ^ 2 / 123) <
      16499 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 123 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_124 :
    barrierV2 124 ^ 2 / 124 < (2754 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 124 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 124 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 124 +
      (4451662 / 100000000) * (-96 / 100) ^ 124 +
      (2545398 / 100000000) * (88 / 100) ^ 124 +
      (-4932634 / 100000000) * (95 / 100) ^ 124 +
      (11618157 / 100000000) * (984 / 1000) ^ 124 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 124 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 124 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 124 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 124 : ℚ) ^ 2 / 124) <
      2754 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 124 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_125 :
    barrierV2 125 ^ 2 / 125 < (1442 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 125 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 125 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 125 +
      (4451662 / 100000000) * (-96 / 100) ^ 125 +
      (2545398 / 100000000) * (88 / 100) ^ 125 +
      (-4932634 / 100000000) * (95 / 100) ^ 125 +
      (11618157 / 100000000) * (984 / 1000) ^ 125 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 125 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 125 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 125 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 125 : ℚ) ^ 2 / 125) <
      1442 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 125 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_126 :
    barrierV2 126 ^ 2 / 126 < (1325 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 126 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 126 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 126 +
      (4451662 / 100000000) * (-96 / 100) ^ 126 +
      (2545398 / 100000000) * (88 / 100) ^ 126 +
      (-4932634 / 100000000) * (95 / 100) ^ 126 +
      (11618157 / 100000000) * (984 / 1000) ^ 126 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 126 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 126 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 126 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 126 : ℚ) ^ 2 / 126) <
      1325 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 126 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_127 :
    barrierV2 127 ^ 2 / 127 < (14099 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 127 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 127 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 127 +
      (4451662 / 100000000) * (-96 / 100) ^ 127 +
      (2545398 / 100000000) * (88 / 100) ^ 127 +
      (-4932634 / 100000000) * (95 / 100) ^ 127 +
      (11618157 / 100000000) * (984 / 1000) ^ 127 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 127 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 127 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 127 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 127 : ℚ) ^ 2 / 127) <
      14099 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 127 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_128 :
    barrierV2 128 ^ 2 / 128 < (2348 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 128 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 128 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 128 +
      (4451662 / 100000000) * (-96 / 100) ^ 128 +
      (2545398 / 100000000) * (88 / 100) ^ 128 +
      (-4932634 / 100000000) * (95 / 100) ^ 128 +
      (11618157 / 100000000) * (984 / 1000) ^ 128 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 128 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 128 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 128 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 128 : ℚ) ^ 2 / 128) <
      2348 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 128 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_128 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (120 + k + 1) ^ 2 / ((120 + k + 1 : ℕ) : ℝ)) ≤
      (41725 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_121.le) barrierV2_norm_term_122.le) barrierV2_norm_term_123.le) barrierV2_norm_term_124.le) barrierV2_norm_term_125.le) barrierV2_norm_term_126.le) barrierV2_norm_term_127.le) barrierV2_norm_term_128.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_128 :
    (∑ k ∈ Finset.range 128,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291533320 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (120 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_120 barrierV2_norm_block_128
  have hc : (1291491595 / 1000000000 : ℝ) + 41725 / 1000000000 =
      1291533320 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_129 :
    barrierV2 129 ^ 2 / 129 < (1229 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 129 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 129 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 129 +
      (4451662 / 100000000) * (-96 / 100) ^ 129 +
      (2545398 / 100000000) * (88 / 100) ^ 129 +
      (-4932634 / 100000000) * (95 / 100) ^ 129 +
      (11618157 / 100000000) * (984 / 1000) ^ 129 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 129 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 129 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 129 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 129 : ℚ) ^ 2 / 129) <
      1229 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 129 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_130 :
    barrierV2 130 ^ 2 / 130 < (1122 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 130 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 130 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 130 +
      (4451662 / 100000000) * (-96 / 100) ^ 130 +
      (2545398 / 100000000) * (88 / 100) ^ 130 +
      (-4932634 / 100000000) * (95 / 100) ^ 130 +
      (11618157 / 100000000) * (984 / 1000) ^ 130 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 130 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 130 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 130 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 130 : ℚ) ^ 2 / 130) <
      1122 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 130 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_131 :
    barrierV2 131 ^ 2 / 131 < (12054 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 131 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 131 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 131 +
      (4451662 / 100000000) * (-96 / 100) ^ 131 +
      (2545398 / 100000000) * (88 / 100) ^ 131 +
      (-4932634 / 100000000) * (95 / 100) ^ 131 +
      (11618157 / 100000000) * (984 / 1000) ^ 131 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 131 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 131 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 131 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 131 : ℚ) ^ 2 / 131) <
      12054 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 131 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_132 :
    barrierV2 132 ^ 2 / 132 < (2003 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 132 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 132 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 132 +
      (4451662 / 100000000) * (-96 / 100) ^ 132 +
      (2545398 / 100000000) * (88 / 100) ^ 132 +
      (-4932634 / 100000000) * (95 / 100) ^ 132 +
      (11618157 / 100000000) * (984 / 1000) ^ 132 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 132 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 132 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 132 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 132 : ℚ) ^ 2 / 132) <
      2003 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 132 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_133 :
    barrierV2 133 ^ 2 / 133 < (1049 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 133 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 133 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 133 +
      (4451662 / 100000000) * (-96 / 100) ^ 133 +
      (2545398 / 100000000) * (88 / 100) ^ 133 +
      (-4932634 / 100000000) * (95 / 100) ^ 133 +
      (11618157 / 100000000) * (984 / 1000) ^ 133 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 133 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 133 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 133 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 133 : ℚ) ^ 2 / 133) <
      1049 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 133 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_134 :
    barrierV2 134 ^ 2 / 134 < (952 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 134 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 134 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 134 +
      (4451662 / 100000000) * (-96 / 100) ^ 134 +
      (2545398 / 100000000) * (88 / 100) ^ 134 +
      (-4932634 / 100000000) * (95 / 100) ^ 134 +
      (11618157 / 100000000) * (984 / 1000) ^ 134 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 134 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 134 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 134 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 134 : ℚ) ^ 2 / 134) <
      952 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 134 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_135 :
    barrierV2 135 ^ 2 / 135 < (10312 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 135 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 135 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 135 +
      (4451662 / 100000000) * (-96 / 100) ^ 135 +
      (2545398 / 100000000) * (88 / 100) ^ 135 +
      (-4932634 / 100000000) * (95 / 100) ^ 135 +
      (11618157 / 100000000) * (984 / 1000) ^ 135 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 135 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 135 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 135 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 135 : ℚ) ^ 2 / 135) <
      10312 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 135 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_136 :
    barrierV2 136 ^ 2 / 136 < (1710 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 136 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 136 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 136 +
      (4451662 / 100000000) * (-96 / 100) ^ 136 +
      (2545398 / 100000000) * (88 / 100) ^ 136 +
      (-4932634 / 100000000) * (95 / 100) ^ 136 +
      (11618157 / 100000000) * (984 / 1000) ^ 136 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 136 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 136 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 136 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 136 : ℚ) ^ 2 / 136) <
      1710 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 136 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_136 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (128 + k + 1) ^ 2 / ((128 + k + 1 : ℕ) : ℝ)) ≤
      (30431 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_129.le) barrierV2_norm_term_130.le) barrierV2_norm_term_131.le) barrierV2_norm_term_132.le) barrierV2_norm_term_133.le) barrierV2_norm_term_134.le) barrierV2_norm_term_135.le) barrierV2_norm_term_136.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_136 :
    (∑ k ∈ Finset.range 136,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291563751 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (128 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_128 barrierV2_norm_block_136
  have hc : (1291533320 / 1000000000 : ℝ) + 30431 / 1000000000 =
      1291563751 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_137 :
    barrierV2 137 ^ 2 / 137 < (895 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 137 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 137 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 137 +
      (4451662 / 100000000) * (-96 / 100) ^ 137 +
      (2545398 / 100000000) * (88 / 100) ^ 137 +
      (-4932634 / 100000000) * (95 / 100) ^ 137 +
      (11618157 / 100000000) * (984 / 1000) ^ 137 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 137 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 137 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 137 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 137 : ℚ) ^ 2 / 137) <
      895 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 137 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_138 :
    barrierV2 138 ^ 2 / 138 < (809 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 138 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 138 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 138 +
      (4451662 / 100000000) * (-96 / 100) ^ 138 +
      (2545398 / 100000000) * (88 / 100) ^ 138 +
      (-4932634 / 100000000) * (95 / 100) ^ 138 +
      (11618157 / 100000000) * (984 / 1000) ^ 138 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 138 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 138 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 138 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 138 : ℚ) ^ 2 / 138) <
      809 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 138 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_139 :
    barrierV2 139 ^ 2 / 139 < (8827 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 139 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 139 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 139 +
      (4451662 / 100000000) * (-96 / 100) ^ 139 +
      (2545398 / 100000000) * (88 / 100) ^ 139 +
      (-4932634 / 100000000) * (95 / 100) ^ 139 +
      (11618157 / 100000000) * (984 / 1000) ^ 139 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 139 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 139 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 139 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 139 : ℚ) ^ 2 / 139) <
      8827 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 139 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_140 :
    barrierV2 140 ^ 2 / 140 < (1461 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 140 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 140 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 140 +
      (4451662 / 100000000) * (-96 / 100) ^ 140 +
      (2545398 / 100000000) * (88 / 100) ^ 140 +
      (-4932634 / 100000000) * (95 / 100) ^ 140 +
      (11618157 / 100000000) * (984 / 1000) ^ 140 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 140 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 140 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 140 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 140 : ℚ) ^ 2 / 140) <
      1461 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 140 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_141 :
    barrierV2 141 ^ 2 / 141 < (765 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 141 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 141 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 141 +
      (4451662 / 100000000) * (-96 / 100) ^ 141 +
      (2545398 / 100000000) * (88 / 100) ^ 141 +
      (-4932634 / 100000000) * (95 / 100) ^ 141 +
      (11618157 / 100000000) * (984 / 1000) ^ 141 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 141 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 141 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 141 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 141 : ℚ) ^ 2 / 141) <
      765 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 141 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_142 :
    barrierV2 142 ^ 2 / 142 < (688 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 142 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 142 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 142 +
      (4451662 / 100000000) * (-96 / 100) ^ 142 +
      (2545398 / 100000000) * (88 / 100) ^ 142 +
      (-4932634 / 100000000) * (95 / 100) ^ 142 +
      (11618157 / 100000000) * (984 / 1000) ^ 142 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 142 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 142 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 142 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 142 : ℚ) ^ 2 / 142) <
      688 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 142 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one,
    sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_143 :
    barrierV2 143 ^ 2 / 143 < (7559 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 143 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 143 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 143 +
      (4451662 / 100000000) * (-96 / 100) ^ 143 +
      (2545398 / 100000000) * (88 / 100) ^ 143 +
      (-4932634 / 100000000) * (95 / 100) ^ 143 +
      (11618157 / 100000000) * (984 / 1000) ^ 143 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 143 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 143 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 143 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 143 : ℚ) ^ 2 / 143) <
      7559 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 143 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re,
    Complex.I_im, Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero,
    mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_144 :
    barrierV2 144 ^ 2 / 144 < (1249 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 144 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 144 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 144 +
      (4451662 / 100000000) * (-96 / 100) ^ 144 +
      (2545398 / 100000000) * (88 / 100) ^ 144 +
      (-4932634 / 100000000) * (95 / 100) ^ 144 +
      (11618157 / 100000000) * (984 / 1000) ^ 144 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 144 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 144 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 144 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 144 : ℚ) ^ 2 / 144) <
      1249 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 144 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re,
    Complex.one_im, mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_144 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (136 + k + 1) ^ 2 / ((136 + k + 1 : ℕ) : ℝ)) ≤
      (22253 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_137.le) barrierV2_norm_term_138.le) barrierV2_norm_term_139.le) barrierV2_norm_term_140.le) barrierV2_norm_term_141.le) barrierV2_norm_term_142.le) barrierV2_norm_term_143.le) barrierV2_norm_term_144.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_144 :
    (∑ k ∈ Finset.range 144,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291586004 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (136 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_136 barrierV2_norm_block_144
  have hc : (1291563751 / 1000000000 : ℝ) + 22253 / 1000000000 =
      1291586004 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormVPrefix192
namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_145 :
    barrierV2 145 ^ 2 / 145 < (654 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 145 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 145 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 145 +
      (4451662 / 100000000) * (-96 / 100) ^ 145 +
      (2545398 / 100000000) * (88 / 100) ^ 145 +
      (-4932634 / 100000000) * (95 / 100) ^ 145 +
      (11618157 / 100000000) * (984 / 1000) ^ 145 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 145 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 145 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 145 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 145 : ℚ) ^ 2 / 145) <
      654 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 145 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_146 :
    barrierV2 146 ^ 2 / 146 < (586 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 146 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 146 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 146 +
      (4451662 / 100000000) * (-96 / 100) ^ 146 +
      (2545398 / 100000000) * (88 / 100) ^ 146 +
      (-4932634 / 100000000) * (95 / 100) ^ 146 +
      (11618157 / 100000000) * (984 / 1000) ^ 146 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 146 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 146 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 146 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 146 : ℚ) ^ 2 / 146) <
      586 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 146 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_147 :
    barrierV2 147 ^ 2 / 147 < (6477 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 147 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 147 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 147 +
      (4451662 / 100000000) * (-96 / 100) ^ 147 +
      (2545398 / 100000000) * (88 / 100) ^ 147 +
      (-4932634 / 100000000) * (95 / 100) ^ 147 +
      (11618157 / 100000000) * (984 / 1000) ^ 147 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 147 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 147 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 147 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 147 : ℚ) ^ 2 / 147) <
      6477 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 147 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_148 :
    barrierV2 148 ^ 2 / 148 < (1068 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 148 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 148 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 148 +
      (4451662 / 100000000) * (-96 / 100) ^ 148 +
      (2545398 / 100000000) * (88 / 100) ^ 148 +
      (-4932634 / 100000000) * (95 / 100) ^ 148 +
      (11618157 / 100000000) * (984 / 1000) ^ 148 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 148 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 148 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 148 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 148 : ℚ) ^ 2 / 148) <
      1068 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 148 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_149 :
    barrierV2 149 ^ 2 / 149 < (560 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 149 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 149 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 149 +
      (4451662 / 100000000) * (-96 / 100) ^ 149 +
      (2545398 / 100000000) * (88 / 100) ^ 149 +
      (-4932634 / 100000000) * (95 / 100) ^ 149 +
      (11618157 / 100000000) * (984 / 1000) ^ 149 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 149 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 149 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 149 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 149 : ℚ) ^ 2 / 149) <
      560 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 149 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_150 :
    barrierV2 150 ^ 2 / 150 < (499 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 150 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 150 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 150 +
      (4451662 / 100000000) * (-96 / 100) ^ 150 +
      (2545398 / 100000000) * (88 / 100) ^ 150 +
      (-4932634 / 100000000) * (95 / 100) ^ 150 +
      (11618157 / 100000000) * (984 / 1000) ^ 150 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 150 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 150 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 150 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 150 : ℚ) ^ 2 / 150) <
      499 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 150 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_151 :
    barrierV2 151 ^ 2 / 151 < (5553 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 151 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 151 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 151 +
      (4451662 / 100000000) * (-96 / 100) ^ 151 +
      (2545398 / 100000000) * (88 / 100) ^ 151 +
      (-4932634 / 100000000) * (95 / 100) ^ 151 +
      (11618157 / 100000000) * (984 / 1000) ^ 151 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 151 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 151 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 151 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 151 : ℚ) ^ 2 / 151) <
      5553 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 151 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_152 :
    barrierV2 152 ^ 2 / 152 < (915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 152 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 152 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 152 +
      (4451662 / 100000000) * (-96 / 100) ^ 152 +
      (2545398 / 100000000) * (88 / 100) ^ 152 +
      (-4932634 / 100000000) * (95 / 100) ^ 152 +
      (11618157 / 100000000) * (984 / 1000) ^ 152 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 152 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 152 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 152 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 152 : ℚ) ^ 2 / 152) <
      915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 152 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_152 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (144 + k + 1) ^ 2 / ((144 + k + 1 : ℕ) : ℝ)) ≤
      (16312 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_145.le) barrierV2_norm_term_146.le) barrierV2_norm_term_147.le) barrierV2_norm_term_148.le) barrierV2_norm_term_149.le) barrierV2_norm_term_150.le) barrierV2_norm_term_151.le) barrierV2_norm_term_152.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_152 :
    (∑ k ∈ Finset.range 152,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291602316 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (144 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_144 barrierV2_norm_block_152
  have hc : (1291586004 / 1000000000 : ℝ) + 16312 / 1000000000 =
      1291602316 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_153 :
    barrierV2 153 ^ 2 / 153 < (480 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 153 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 153 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 153 +
      (4451662 / 100000000) * (-96 / 100) ^ 153 +
      (2545398 / 100000000) * (88 / 100) ^ 153 +
      (-4932634 / 100000000) * (95 / 100) ^ 153 +
      (11618157 / 100000000) * (984 / 1000) ^ 153 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 153 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 153 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 153 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 153 : ℚ) ^ 2 / 153) <
      480 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 153 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_154 :
    barrierV2 154 ^ 2 / 154 < (426 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 154 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 154 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 154 +
      (4451662 / 100000000) * (-96 / 100) ^ 154 +
      (2545398 / 100000000) * (88 / 100) ^ 154 +
      (-4932634 / 100000000) * (95 / 100) ^ 154 +
      (11618157 / 100000000) * (984 / 1000) ^ 154 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 154 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 154 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 154 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 154 : ℚ) ^ 2 / 154) <
      426 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 154 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_155 :
    barrierV2 155 ^ 2 / 155 < (4763 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 155 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 155 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 155 +
      (4451662 / 100000000) * (-96 / 100) ^ 155 +
      (2545398 / 100000000) * (88 / 100) ^ 155 +
      (-4932634 / 100000000) * (95 / 100) ^ 155 +
      (11618157 / 100000000) * (984 / 1000) ^ 155 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 155 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 155 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 155 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 155 : ℚ) ^ 2 / 155) <
      4763 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 155 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_156 :
    barrierV2 156 ^ 2 / 156 < (784 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 156 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 156 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 156 +
      (4451662 / 100000000) * (-96 / 100) ^ 156 +
      (2545398 / 100000000) * (88 / 100) ^ 156 +
      (-4932634 / 100000000) * (95 / 100) ^ 156 +
      (11618157 / 100000000) * (984 / 1000) ^ 156 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 156 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 156 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 156 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 156 : ℚ) ^ 2 / 156) <
      784 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 156 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_157 :
    barrierV2 157 ^ 2 / 157 < (411 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 157 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 157 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 157 +
      (4451662 / 100000000) * (-96 / 100) ^ 157 +
      (2545398 / 100000000) * (88 / 100) ^ 157 +
      (-4932634 / 100000000) * (95 / 100) ^ 157 +
      (11618157 / 100000000) * (984 / 1000) ^ 157 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 157 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 157 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 157 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 157 : ℚ) ^ 2 / 157) <
      411 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 157 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_158 :
    barrierV2 158 ^ 2 / 158 < (364 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 158 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 158 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 158 +
      (4451662 / 100000000) * (-96 / 100) ^ 158 +
      (2545398 / 100000000) * (88 / 100) ^ 158 +
      (-4932634 / 100000000) * (95 / 100) ^ 158 +
      (11618157 / 100000000) * (984 / 1000) ^ 158 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 158 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 158 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 158 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 158 : ℚ) ^ 2 / 158) <
      364 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 158 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_159 :
    barrierV2 159 ^ 2 / 159 < (4087 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 159 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 159 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 159 +
      (4451662 / 100000000) * (-96 / 100) ^ 159 +
      (2545398 / 100000000) * (88 / 100) ^ 159 +
      (-4932634 / 100000000) * (95 / 100) ^ 159 +
      (11618157 / 100000000) * (984 / 1000) ^ 159 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 159 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 159 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 159 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 159 : ℚ) ^ 2 / 159) <
      4087 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 159 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_160 :
    barrierV2 160 ^ 2 / 160 < (672 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 160 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 160 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 160 +
      (4451662 / 100000000) * (-96 / 100) ^ 160 +
      (2545398 / 100000000) * (88 / 100) ^ 160 +
      (-4932634 / 100000000) * (95 / 100) ^ 160 +
      (11618157 / 100000000) * (984 / 1000) ^ 160 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 160 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 160 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 160 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 160 : ℚ) ^ 2 / 160) <
      672 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 160 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_160 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (152 + k + 1) ^ 2 / ((152 + k + 1 : ℕ) : ℝ)) ≤
      (11987 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_153.le) barrierV2_norm_term_154.le) barrierV2_norm_term_155.le) barrierV2_norm_term_156.le) barrierV2_norm_term_157.le) barrierV2_norm_term_158.le) barrierV2_norm_term_159.le) barrierV2_norm_term_160.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_160 :
    (∑ k ∈ Finset.range 160,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291614303 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (152 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_152 barrierV2_norm_block_160
  have hc : (1291602316 / 1000000000 : ℝ) + 11987 / 1000000000 =
      1291614303 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_161 :
    barrierV2 161 ^ 2 / 161 < (352 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 161 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 161 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 161 +
      (4451662 / 100000000) * (-96 / 100) ^ 161 +
      (2545398 / 100000000) * (88 / 100) ^ 161 +
      (-4932634 / 100000000) * (95 / 100) ^ 161 +
      (11618157 / 100000000) * (984 / 1000) ^ 161 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 161 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 161 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 161 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 161 : ℚ) ^ 2 / 161) <
      352 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 161 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_162 :
    barrierV2 162 ^ 2 / 162 < (311 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 162 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 162 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 162 +
      (4451662 / 100000000) * (-96 / 100) ^ 162 +
      (2545398 / 100000000) * (88 / 100) ^ 162 +
      (-4932634 / 100000000) * (95 / 100) ^ 162 +
      (11618157 / 100000000) * (984 / 1000) ^ 162 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 162 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 162 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 162 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 162 : ℚ) ^ 2 / 162) <
      311 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 162 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_163 :
    barrierV2 163 ^ 2 / 163 < (3509 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 163 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 163 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 163 +
      (4451662 / 100000000) * (-96 / 100) ^ 163 +
      (2545398 / 100000000) * (88 / 100) ^ 163 +
      (-4932634 / 100000000) * (95 / 100) ^ 163 +
      (11618157 / 100000000) * (984 / 1000) ^ 163 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 163 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 163 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 163 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 163 : ℚ) ^ 2 / 163) <
      3509 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 163 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_164 :
    barrierV2 164 ^ 2 / 164 < (576 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 164 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 164 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 164 +
      (4451662 / 100000000) * (-96 / 100) ^ 164 +
      (2545398 / 100000000) * (88 / 100) ^ 164 +
      (-4932634 / 100000000) * (95 / 100) ^ 164 +
      (11618157 / 100000000) * (984 / 1000) ^ 164 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 164 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 164 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 164 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 164 : ℚ) ^ 2 / 164) <
      576 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 164 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_165 :
    barrierV2 165 ^ 2 / 165 < (302 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 165 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 165 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 165 +
      (4451662 / 100000000) * (-96 / 100) ^ 165 +
      (2545398 / 100000000) * (88 / 100) ^ 165 +
      (-4932634 / 100000000) * (95 / 100) ^ 165 +
      (11618157 / 100000000) * (984 / 1000) ^ 165 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 165 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 165 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 165 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 165 : ℚ) ^ 2 / 165) <
      302 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 165 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_166 :
    barrierV2 166 ^ 2 / 166 < (267 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 166 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 166 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 166 +
      (4451662 / 100000000) * (-96 / 100) ^ 166 +
      (2545398 / 100000000) * (88 / 100) ^ 166 +
      (-4932634 / 100000000) * (95 / 100) ^ 166 +
      (11618157 / 100000000) * (984 / 1000) ^ 166 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 166 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 166 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 166 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 166 : ℚ) ^ 2 / 166) <
      267 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 166 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_167 :
    barrierV2 167 ^ 2 / 167 < (3014 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 167 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 167 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 167 +
      (4451662 / 100000000) * (-96 / 100) ^ 167 +
      (2545398 / 100000000) * (88 / 100) ^ 167 +
      (-4932634 / 100000000) * (95 / 100) ^ 167 +
      (11618157 / 100000000) * (984 / 1000) ^ 167 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 167 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 167 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 167 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 167 : ℚ) ^ 2 / 167) <
      3014 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 167 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_168 :
    barrierV2 168 ^ 2 / 168 < (494 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 168 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 168 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 168 +
      (4451662 / 100000000) * (-96 / 100) ^ 168 +
      (2545398 / 100000000) * (88 / 100) ^ 168 +
      (-4932634 / 100000000) * (95 / 100) ^ 168 +
      (11618157 / 100000000) * (984 / 1000) ^ 168 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 168 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 168 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 168 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 168 : ℚ) ^ 2 / 168) <
      494 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 168 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_168 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (160 + k + 1) ^ 2 / ((160 + k + 1 : ℕ) : ℝ)) ≤
      (8825 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_161.le) barrierV2_norm_term_162.le) barrierV2_norm_term_163.le) barrierV2_norm_term_164.le) barrierV2_norm_term_165.le) barrierV2_norm_term_166.le) barrierV2_norm_term_167.le) barrierV2_norm_term_168.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_168 :
    (∑ k ∈ Finset.range 168,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291623128 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (160 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_160 barrierV2_norm_block_168
  have hc : (1291614303 / 1000000000 : ℝ) + 8825 / 1000000000 =
      1291623128 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_169 :
    barrierV2 169 ^ 2 / 169 < (260 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 169 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 169 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 169 +
      (4451662 / 100000000) * (-96 / 100) ^ 169 +
      (2545398 / 100000000) * (88 / 100) ^ 169 +
      (-4932634 / 100000000) * (95 / 100) ^ 169 +
      (11618157 / 100000000) * (984 / 1000) ^ 169 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 169 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 169 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 169 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 169 : ℚ) ^ 2 / 169) <
      260 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 169 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_170 :
    barrierV2 170 ^ 2 / 170 < (228 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 170 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 170 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 170 +
      (4451662 / 100000000) * (-96 / 100) ^ 170 +
      (2545398 / 100000000) * (88 / 100) ^ 170 +
      (-4932634 / 100000000) * (95 / 100) ^ 170 +
      (11618157 / 100000000) * (984 / 1000) ^ 170 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 170 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 170 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 170 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 170 : ℚ) ^ 2 / 170) <
      228 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 170 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_171 :
    barrierV2 171 ^ 2 / 171 < (2590 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 171 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 171 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 171 +
      (4451662 / 100000000) * (-96 / 100) ^ 171 +
      (2545398 / 100000000) * (88 / 100) ^ 171 +
      (-4932634 / 100000000) * (95 / 100) ^ 171 +
      (11618157 / 100000000) * (984 / 1000) ^ 171 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 171 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 171 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 171 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 171 : ℚ) ^ 2 / 171) <
      2590 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 171 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_172 :
    barrierV2 172 ^ 2 / 172 < (424 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 172 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 172 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 172 +
      (4451662 / 100000000) * (-96 / 100) ^ 172 +
      (2545398 / 100000000) * (88 / 100) ^ 172 +
      (-4932634 / 100000000) * (95 / 100) ^ 172 +
      (11618157 / 100000000) * (984 / 1000) ^ 172 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 172 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 172 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 172 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 172 : ℚ) ^ 2 / 172) <
      424 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 172 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_173 :
    barrierV2 173 ^ 2 / 173 < (223 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 173 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 173 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 173 +
      (4451662 / 100000000) * (-96 / 100) ^ 173 +
      (2545398 / 100000000) * (88 / 100) ^ 173 +
      (-4932634 / 100000000) * (95 / 100) ^ 173 +
      (11618157 / 100000000) * (984 / 1000) ^ 173 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 173 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 173 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 173 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 173 : ℚ) ^ 2 / 173) <
      223 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 173 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_174 :
    barrierV2 174 ^ 2 / 174 < (196 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 174 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 174 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 174 +
      (4451662 / 100000000) * (-96 / 100) ^ 174 +
      (2545398 / 100000000) * (88 / 100) ^ 174 +
      (-4932634 / 100000000) * (95 / 100) ^ 174 +
      (11618157 / 100000000) * (984 / 1000) ^ 174 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 174 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 174 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 174 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 174 : ℚ) ^ 2 / 174) <
      196 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 174 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_175 :
    barrierV2 175 ^ 2 / 175 < (2227 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 175 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 175 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 175 +
      (4451662 / 100000000) * (-96 / 100) ^ 175 +
      (2545398 / 100000000) * (88 / 100) ^ 175 +
      (-4932634 / 100000000) * (95 / 100) ^ 175 +
      (11618157 / 100000000) * (984 / 1000) ^ 175 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 175 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 175 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 175 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 175 : ℚ) ^ 2 / 175) <
      2227 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 175 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_176 :
    barrierV2 176 ^ 2 / 176 < (365 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 176 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 176 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 176 +
      (4451662 / 100000000) * (-96 / 100) ^ 176 +
      (2545398 / 100000000) * (88 / 100) ^ 176 +
      (-4932634 / 100000000) * (95 / 100) ^ 176 +
      (11618157 / 100000000) * (984 / 1000) ^ 176 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 176 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 176 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 176 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 176 : ℚ) ^ 2 / 176) <
      365 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 176 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_176 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (168 + k + 1) ^ 2 / ((168 + k + 1 : ℕ) : ℝ)) ≤
      (6513 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_169.le) barrierV2_norm_term_170.le) barrierV2_norm_term_171.le) barrierV2_norm_term_172.le) barrierV2_norm_term_173.le) barrierV2_norm_term_174.le) barrierV2_norm_term_175.le) barrierV2_norm_term_176.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_176 :
    (∑ k ∈ Finset.range 176,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291629641 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (168 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_168 barrierV2_norm_block_176
  have hc : (1291623128 / 1000000000 : ℝ) + 6513 / 1000000000 =
      1291629641 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_177 :
    barrierV2 177 ^ 2 / 177 < (192 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 177 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 177 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 177 +
      (4451662 / 100000000) * (-96 / 100) ^ 177 +
      (2545398 / 100000000) * (88 / 100) ^ 177 +
      (-4932634 / 100000000) * (95 / 100) ^ 177 +
      (11618157 / 100000000) * (984 / 1000) ^ 177 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 177 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 177 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 177 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 177 : ℚ) ^ 2 / 177) <
      192 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 177 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_178 :
    barrierV2 178 ^ 2 / 178 < (168 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 178 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 178 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 178 +
      (4451662 / 100000000) * (-96 / 100) ^ 178 +
      (2545398 / 100000000) * (88 / 100) ^ 178 +
      (-4932634 / 100000000) * (95 / 100) ^ 178 +
      (11618157 / 100000000) * (984 / 1000) ^ 178 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 178 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 178 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 178 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 178 : ℚ) ^ 2 / 178) <
      168 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 178 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_179 :
    barrierV2 179 ^ 2 / 179 < (1915 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 179 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 179 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 179 +
      (4451662 / 100000000) * (-96 / 100) ^ 179 +
      (2545398 / 100000000) * (88 / 100) ^ 179 +
      (-4932634 / 100000000) * (95 / 100) ^ 179 +
      (11618157 / 100000000) * (984 / 1000) ^ 179 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 179 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 179 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 179 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 179 : ℚ) ^ 2 / 179) <
      1915 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 179 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_180 :
    barrierV2 180 ^ 2 / 180 < (313 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 180 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 180 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 180 +
      (4451662 / 100000000) * (-96 / 100) ^ 180 +
      (2545398 / 100000000) * (88 / 100) ^ 180 +
      (-4932634 / 100000000) * (95 / 100) ^ 180 +
      (11618157 / 100000000) * (984 / 1000) ^ 180 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 180 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 180 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 180 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 180 : ℚ) ^ 2 / 180) <
      313 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 180 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_181 :
    barrierV2 181 ^ 2 / 181 < (165 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 181 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 181 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 181 +
      (4451662 / 100000000) * (-96 / 100) ^ 181 +
      (2545398 / 100000000) * (88 / 100) ^ 181 +
      (-4932634 / 100000000) * (95 / 100) ^ 181 +
      (11618157 / 100000000) * (984 / 1000) ^ 181 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 181 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 181 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 181 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 181 : ℚ) ^ 2 / 181) <
      165 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 181 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_182 :
    barrierV2 182 ^ 2 / 182 < (144 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 182 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 182 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 182 +
      (4451662 / 100000000) * (-96 / 100) ^ 182 +
      (2545398 / 100000000) * (88 / 100) ^ 182 +
      (-4932634 / 100000000) * (95 / 100) ^ 182 +
      (11618157 / 100000000) * (984 / 1000) ^ 182 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 182 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 182 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 182 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 182 : ℚ) ^ 2 / 182) <
      144 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 182 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_183 :
    barrierV2 183 ^ 2 / 183 < (1648 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 183 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 183 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 183 +
      (4451662 / 100000000) * (-96 / 100) ^ 183 +
      (2545398 / 100000000) * (88 / 100) ^ 183 +
      (-4932634 / 100000000) * (95 / 100) ^ 183 +
      (11618157 / 100000000) * (984 / 1000) ^ 183 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 183 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 183 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 183 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 183 : ℚ) ^ 2 / 183) <
      1648 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 183 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_184 :
    barrierV2 184 ^ 2 / 184 < (270 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 184 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 184 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 184 +
      (4451662 / 100000000) * (-96 / 100) ^ 184 +
      (2545398 / 100000000) * (88 / 100) ^ 184 +
      (-4932634 / 100000000) * (95 / 100) ^ 184 +
      (11618157 / 100000000) * (984 / 1000) ^ 184 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 184 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 184 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 184 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 184 : ℚ) ^ 2 / 184) <
      270 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 184 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_184 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (176 + k + 1) ^ 2 / ((176 + k + 1 : ℕ) : ℝ)) ≤
      (4815 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_177.le) barrierV2_norm_term_178.le) barrierV2_norm_term_179.le) barrierV2_norm_term_180.le) barrierV2_norm_term_181.le) barrierV2_norm_term_182.le) barrierV2_norm_term_183.le) barrierV2_norm_term_184.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_184 :
    (∑ k ∈ Finset.range 184,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291634456 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (176 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_176 barrierV2_norm_block_184
  have hc : (1291629641 / 1000000000 : ℝ) + 4815 / 1000000000 =
      1291634456 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_185 :
    barrierV2 185 ^ 2 / 185 < (142 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 185 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 185 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 185 +
      (4451662 / 100000000) * (-96 / 100) ^ 185 +
      (2545398 / 100000000) * (88 / 100) ^ 185 +
      (-4932634 / 100000000) * (95 / 100) ^ 185 +
      (11618157 / 100000000) * (984 / 1000) ^ 185 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 185 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 185 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 185 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 185 : ℚ) ^ 2 / 185) <
      142 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 185 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_186 :
    barrierV2 186 ^ 2 / 186 < (124 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 186 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 186 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 186 +
      (4451662 / 100000000) * (-96 / 100) ^ 186 +
      (2545398 / 100000000) * (88 / 100) ^ 186 +
      (-4932634 / 100000000) * (95 / 100) ^ 186 +
      (11618157 / 100000000) * (984 / 1000) ^ 186 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 186 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 186 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 186 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 186 : ℚ) ^ 2 / 186) <
      124 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 186 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_187 :
    barrierV2 187 ^ 2 / 187 < (1418 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 187 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 187 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 187 +
      (4451662 / 100000000) * (-96 / 100) ^ 187 +
      (2545398 / 100000000) * (88 / 100) ^ 187 +
      (-4932634 / 100000000) * (95 / 100) ^ 187 +
      (11618157 / 100000000) * (984 / 1000) ^ 187 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 187 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 187 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 187 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 187 : ℚ) ^ 2 / 187) <
      1418 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 187 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_188 :
    barrierV2 188 ^ 2 / 188 < (232 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 188 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 188 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 188 +
      (4451662 / 100000000) * (-96 / 100) ^ 188 +
      (2545398 / 100000000) * (88 / 100) ^ 188 +
      (-4932634 / 100000000) * (95 / 100) ^ 188 +
      (11618157 / 100000000) * (984 / 1000) ^ 188 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 188 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 188 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 188 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 188 : ℚ) ^ 2 / 188) <
      232 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 188 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_189 :
    barrierV2 189 ^ 2 / 189 < (122 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 189 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 189 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 189 +
      (4451662 / 100000000) * (-96 / 100) ^ 189 +
      (2545398 / 100000000) * (88 / 100) ^ 189 +
      (-4932634 / 100000000) * (95 / 100) ^ 189 +
      (11618157 / 100000000) * (984 / 1000) ^ 189 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 189 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 189 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 189 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 189 : ℚ) ^ 2 / 189) <
      122 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 189 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_190 :
    barrierV2 190 ^ 2 / 190 < (107 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 190 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 190 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 190 +
      (4451662 / 100000000) * (-96 / 100) ^ 190 +
      (2545398 / 100000000) * (88 / 100) ^ 190 +
      (-4932634 / 100000000) * (95 / 100) ^ 190 +
      (11618157 / 100000000) * (984 / 1000) ^ 190 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 190 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 190 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 190 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 190 : ℚ) ^ 2 / 190) <
      107 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 190 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_191 :
    barrierV2 191 ^ 2 / 191 < (1221 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 191 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 191 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 191 +
      (4451662 / 100000000) * (-96 / 100) ^ 191 +
      (2545398 / 100000000) * (88 / 100) ^ 191 +
      (-4932634 / 100000000) * (95 / 100) ^ 191 +
      (11618157 / 100000000) * (984 / 1000) ^ 191 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 191 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 191 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 191 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 191 : ℚ) ^ 2 / 191) <
      1221 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 191 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg, mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_192 :
    barrierV2 192 ^ 2 / 192 < (200 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 192 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 192 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 192 +
      (4451662 / 100000000) * (-96 / 100) ^ 192 +
      (2545398 / 100000000) * (88 / 100) ^ 192 +
      (-4932634 / 100000000) * (95 / 100) ^ 192 +
      (11618157 / 100000000) * (984 / 1000) ^ 192 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 192 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 192 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 192 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 192 : ℚ) ^ 2 / 192) <
      200 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 192 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi, Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_192 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (184 + k + 1) ^ 2 / ((184 + k + 1 : ℕ) : ℝ)) ≤
      (3566 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_185.le) barrierV2_norm_term_186.le) barrierV2_norm_term_187.le) barrierV2_norm_term_188.le) barrierV2_norm_term_189.le) barrierV2_norm_term_190.le) barrierV2_norm_term_191.le) barrierV2_norm_term_192.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_192 :
    (∑ k ∈ Finset.range 192,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291638022 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (184 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_184 barrierV2_norm_block_192
  have hc : (1291634456 / 1000000000 : ℝ) + 3566 / 1000000000 =
      1291638022 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierTwoNormVPrefix225
namespace OAI


noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_193 :
    barrierV2 193 ^ 2 / 193 < (105 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 193 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 193 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 193 +
      (4451662 / 100000000) * (-96 / 100) ^ 193 +
      (2545398 / 100000000) * (88 / 100) ^ 193 +
      (-4932634 / 100000000) * (95 / 100) ^ 193 +
      (11618157 / 100000000) * (984 / 1000) ^ 193 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 193 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 193 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 193 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 193 : ℚ) ^ 2 / 193) <
      105 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 193 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_194 :
    barrierV2 194 ^ 2 / 194 < (92 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 194 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 194 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 194 +
      (4451662 / 100000000) * (-96 / 100) ^ 194 +
      (2545398 / 100000000) * (88 / 100) ^ 194 +
      (-4932634 / 100000000) * (95 / 100) ^ 194 +
      (11618157 / 100000000) * (984 / 1000) ^ 194 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 194 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 194 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 194 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 194 : ℚ) ^ 2 / 194) <
      92 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 194 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_195 :
    barrierV2 195 ^ 2 / 195 < (1052 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 195 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 195 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 195 +
      (4451662 / 100000000) * (-96 / 100) ^ 195 +
      (2545398 / 100000000) * (88 / 100) ^ 195 +
      (-4932634 / 100000000) * (95 / 100) ^ 195 +
      (11618157 / 100000000) * (984 / 1000) ^ 195 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 195 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 195 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 195 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 195 : ℚ) ^ 2 / 195) <
      1052 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 195 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_196 :
    barrierV2 196 ^ 2 / 196 < (172 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 196 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 196 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 196 +
      (4451662 / 100000000) * (-96 / 100) ^ 196 +
      (2545398 / 100000000) * (88 / 100) ^ 196 +
      (-4932634 / 100000000) * (95 / 100) ^ 196 +
      (11618157 / 100000000) * (984 / 1000) ^ 196 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 196 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 196 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 196 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 196 : ℚ) ^ 2 / 196) <
      172 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 196 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_197 :
    barrierV2 197 ^ 2 / 197 < (91 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 197 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 197 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 197 +
      (4451662 / 100000000) * (-96 / 100) ^ 197 +
      (2545398 / 100000000) * (88 / 100) ^ 197 +
      (-4932634 / 100000000) * (95 / 100) ^ 197 +
      (11618157 / 100000000) * (984 / 1000) ^ 197 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 197 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 197 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 197 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 197 : ℚ) ^ 2 / 197) <
      91 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 197 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_198 :
    barrierV2 198 ^ 2 / 198 < (79 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 198 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 198 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 198 +
      (4451662 / 100000000) * (-96 / 100) ^ 198 +
      (2545398 / 100000000) * (88 / 100) ^ 198 +
      (-4932634 / 100000000) * (95 / 100) ^ 198 +
      (11618157 / 100000000) * (984 / 1000) ^ 198 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 198 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 198 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 198 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 198 : ℚ) ^ 2 / 198) <
      79 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 198 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_199 :
    barrierV2 199 ^ 2 / 199 < (907 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 199 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 199 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 199 +
      (4451662 / 100000000) * (-96 / 100) ^ 199 +
      (2545398 / 100000000) * (88 / 100) ^ 199 +
      (-4932634 / 100000000) * (95 / 100) ^ 199 +
      (11618157 / 100000000) * (984 / 1000) ^ 199 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 199 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 199 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 199 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 199 : ℚ) ^ 2 / 199) <
      907 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 199 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_200 :
    barrierV2 200 ^ 2 / 200 < (148 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 200 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 200 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 200 +
      (4451662 / 100000000) * (-96 / 100) ^ 200 +
      (2545398 / 100000000) * (88 / 100) ^ 200 +
      (-4932634 / 100000000) * (95 / 100) ^ 200 +
      (11618157 / 100000000) * (984 / 1000) ^ 200 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 200 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 200 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 200 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 200 : ℚ) ^ 2 / 200) <
      148 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 200 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_200 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (192 + k + 1) ^ 2 / ((192 + k + 1 : ℕ) : ℝ)) ≤
      (2646 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_193.le) barrierV2_norm_term_194.le) barrierV2_norm_term_195.le) barrierV2_norm_term_196.le) barrierV2_norm_term_197.le) barrierV2_norm_term_198.le) barrierV2_norm_term_199.le) barrierV2_norm_term_200.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_200 :
    (∑ k ∈ Finset.range 200,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291640668 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (192 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_192 barrierV2_norm_block_200
  have hc : (1291638022 / 1000000000 : ℝ) + 2646 / 1000000000 =
      1291640668 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_201 :
    barrierV2 201 ^ 2 / 201 < (78 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 201 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 201 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 201 +
      (4451662 / 100000000) * (-96 / 100) ^ 201 +
      (2545398 / 100000000) * (88 / 100) ^ 201 +
      (-4932634 / 100000000) * (95 / 100) ^ 201 +
      (11618157 / 100000000) * (984 / 1000) ^ 201 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 201 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 201 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 201 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 201 : ℚ) ^ 2 / 201) <
      78 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 201 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_202 :
    barrierV2 202 ^ 2 / 202 < (68 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 202 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 202 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 202 +
      (4451662 / 100000000) * (-96 / 100) ^ 202 +
      (2545398 / 100000000) * (88 / 100) ^ 202 +
      (-4932634 / 100000000) * (95 / 100) ^ 202 +
      (11618157 / 100000000) * (984 / 1000) ^ 202 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 202 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 202 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 202 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 202 : ℚ) ^ 2 / 202) <
      68 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 202 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_203 :
    barrierV2 203 ^ 2 / 203 < (782 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 203 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 203 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 203 +
      (4451662 / 100000000) * (-96 / 100) ^ 203 +
      (2545398 / 100000000) * (88 / 100) ^ 203 +
      (-4932634 / 100000000) * (95 / 100) ^ 203 +
      (11618157 / 100000000) * (984 / 1000) ^ 203 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 203 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 203 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 203 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 203 : ℚ) ^ 2 / 203) <
      782 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 203 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_204 :
    barrierV2 204 ^ 2 / 204 < (128 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 204 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 204 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 204 +
      (4451662 / 100000000) * (-96 / 100) ^ 204 +
      (2545398 / 100000000) * (88 / 100) ^ 204 +
      (-4932634 / 100000000) * (95 / 100) ^ 204 +
      (11618157 / 100000000) * (984 / 1000) ^ 204 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 204 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 204 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 204 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 204 : ℚ) ^ 2 / 204) <
      128 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 204 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_205 :
    barrierV2 205 ^ 2 / 205 < (67 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 205 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 205 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 205 +
      (4451662 / 100000000) * (-96 / 100) ^ 205 +
      (2545398 / 100000000) * (88 / 100) ^ 205 +
      (-4932634 / 100000000) * (95 / 100) ^ 205 +
      (11618157 / 100000000) * (984 / 1000) ^ 205 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 205 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 205 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 205 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 205 : ℚ) ^ 2 / 205) <
      67 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 205 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_206 :
    barrierV2 206 ^ 2 / 206 < (59 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 206 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 206 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 206 +
      (4451662 / 100000000) * (-96 / 100) ^ 206 +
      (2545398 / 100000000) * (88 / 100) ^ 206 +
      (-4932634 / 100000000) * (95 / 100) ^ 206 +
      (11618157 / 100000000) * (984 / 1000) ^ 206 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 206 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 206 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 206 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 206 : ℚ) ^ 2 / 206) <
      59 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 206 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_207 :
    barrierV2 207 ^ 2 / 207 < (674 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 207 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 207 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 207 +
      (4451662 / 100000000) * (-96 / 100) ^ 207 +
      (2545398 / 100000000) * (88 / 100) ^ 207 +
      (-4932634 / 100000000) * (95 / 100) ^ 207 +
      (11618157 / 100000000) * (984 / 1000) ^ 207 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 207 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 207 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 207 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 207 : ℚ) ^ 2 / 207) <
      674 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 207 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_208 :
    barrierV2 208 ^ 2 / 208 < (110 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 208 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 208 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 208 +
      (4451662 / 100000000) * (-96 / 100) ^ 208 +
      (2545398 / 100000000) * (88 / 100) ^ 208 +
      (-4932634 / 100000000) * (95 / 100) ^ 208 +
      (11618157 / 100000000) * (984 / 1000) ^ 208 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 208 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 208 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 208 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 208 : ℚ) ^ 2 / 208) <
      110 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 208 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_208 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (200 + k + 1) ^ 2 / ((200 + k + 1 : ℕ) : ℝ)) ≤
      (1966 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_201.le) barrierV2_norm_term_202.le) barrierV2_norm_term_203.le) barrierV2_norm_term_204.le) barrierV2_norm_term_205.le) barrierV2_norm_term_206.le) barrierV2_norm_term_207.le) barrierV2_norm_term_208.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_208 :
    (∑ k ∈ Finset.range 208,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291642634 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (200 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_200 barrierV2_norm_block_208
  have hc : (1291640668 / 1000000000 : ℝ) + 1966 / 1000000000 =
      1291642634 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_209 :
    barrierV2 209 ^ 2 / 209 < (58 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 209 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 209 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 209 +
      (4451662 / 100000000) * (-96 / 100) ^ 209 +
      (2545398 / 100000000) * (88 / 100) ^ 209 +
      (-4932634 / 100000000) * (95 / 100) ^ 209 +
      (11618157 / 100000000) * (984 / 1000) ^ 209 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 209 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 209 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 209 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 209 : ℚ) ^ 2 / 209) <
      58 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 209 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_210 :
    barrierV2 210 ^ 2 / 210 < (51 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 210 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 210 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 210 +
      (4451662 / 100000000) * (-96 / 100) ^ 210 +
      (2545398 / 100000000) * (88 / 100) ^ 210 +
      (-4932634 / 100000000) * (95 / 100) ^ 210 +
      (11618157 / 100000000) * (984 / 1000) ^ 210 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 210 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 210 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 210 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 210 : ℚ) ^ 2 / 210) <
      51 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 210 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_211 :
    barrierV2 211 ^ 2 / 211 < (581 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 211 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 211 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 211 +
      (4451662 / 100000000) * (-96 / 100) ^ 211 +
      (2545398 / 100000000) * (88 / 100) ^ 211 +
      (-4932634 / 100000000) * (95 / 100) ^ 211 +
      (11618157 / 100000000) * (984 / 1000) ^ 211 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 211 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 211 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 211 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 211 : ℚ) ^ 2 / 211) <
      581 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 211 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_212 :
    barrierV2 212 ^ 2 / 212 < (95 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 212 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 212 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 212 +
      (4451662 / 100000000) * (-96 / 100) ^ 212 +
      (2545398 / 100000000) * (88 / 100) ^ 212 +
      (-4932634 / 100000000) * (95 / 100) ^ 212 +
      (11618157 / 100000000) * (984 / 1000) ^ 212 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 212 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 212 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 212 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 212 : ℚ) ^ 2 / 212) <
      95 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 212 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_213 :
    barrierV2 213 ^ 2 / 213 < (50 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 213 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 213 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 213 +
      (4451662 / 100000000) * (-96 / 100) ^ 213 +
      (2545398 / 100000000) * (88 / 100) ^ 213 +
      (-4932634 / 100000000) * (95 / 100) ^ 213 +
      (11618157 / 100000000) * (984 / 1000) ^ 213 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 213 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 213 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 213 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 213 : ℚ) ^ 2 / 213) <
      50 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 213 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_214 :
    barrierV2 214 ^ 2 / 214 < (44 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 214 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 214 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 214 +
      (4451662 / 100000000) * (-96 / 100) ^ 214 +
      (2545398 / 100000000) * (88 / 100) ^ 214 +
      (-4932634 / 100000000) * (95 / 100) ^ 214 +
      (11618157 / 100000000) * (984 / 1000) ^ 214 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 214 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 214 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 214 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 214 : ℚ) ^ 2 / 214) <
      44 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 214 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_215 :
    barrierV2 215 ^ 2 / 215 < (502 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 215 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 215 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 215 +
      (4451662 / 100000000) * (-96 / 100) ^ 215 +
      (2545398 / 100000000) * (88 / 100) ^ 215 +
      (-4932634 / 100000000) * (95 / 100) ^ 215 +
      (11618157 / 100000000) * (984 / 1000) ^ 215 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 215 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 215 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 215 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 215 : ℚ) ^ 2 / 215) <
      502 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 215 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_216 :
    barrierV2 216 ^ 2 / 216 < (82 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 216 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 216 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 216 +
      (4451662 / 100000000) * (-96 / 100) ^ 216 +
      (2545398 / 100000000) * (88 / 100) ^ 216 +
      (-4932634 / 100000000) * (95 / 100) ^ 216 +
      (11618157 / 100000000) * (984 / 1000) ^ 216 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 216 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 216 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 216 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 216 : ℚ) ^ 2 / 216) <
      82 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 216 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_216 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (208 + k + 1) ^ 2 / ((208 + k + 1 : ℕ) : ℝ)) ≤
      (1463 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_209.le) barrierV2_norm_term_210.le) barrierV2_norm_term_211.le) barrierV2_norm_term_212.le) barrierV2_norm_term_213.le) barrierV2_norm_term_214.le) barrierV2_norm_term_215.le) barrierV2_norm_term_216.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_216 :
    (∑ k ∈ Finset.range 216,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291644097 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (208 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_208 barrierV2_norm_block_216
  have hc : (1291642634 / 1000000000 : ℝ) + 1463 / 1000000000 =
      1291644097 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_217 :
    barrierV2 217 ^ 2 / 217 < (43 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 217 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 217 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 217 +
      (4451662 / 100000000) * (-96 / 100) ^ 217 +
      (2545398 / 100000000) * (88 / 100) ^ 217 +
      (-4932634 / 100000000) * (95 / 100) ^ 217 +
      (11618157 / 100000000) * (984 / 1000) ^ 217 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 217 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 217 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 217 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 217 : ℚ) ^ 2 / 217) <
      43 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 217 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_218 :
    barrierV2 218 ^ 2 / 218 < (38 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 218 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 218 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 218 +
      (4451662 / 100000000) * (-96 / 100) ^ 218 +
      (2545398 / 100000000) * (88 / 100) ^ 218 +
      (-4932634 / 100000000) * (95 / 100) ^ 218 +
      (11618157 / 100000000) * (984 / 1000) ^ 218 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 218 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 218 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 218 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 218 : ℚ) ^ 2 / 218) <
      38 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 218 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_219 :
    barrierV2 219 ^ 2 / 219 < (433 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 219 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 219 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 219 +
      (4451662 / 100000000) * (-96 / 100) ^ 219 +
      (2545398 / 100000000) * (88 / 100) ^ 219 +
      (-4932634 / 100000000) * (95 / 100) ^ 219 +
      (11618157 / 100000000) * (984 / 1000) ^ 219 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 219 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 219 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 219 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 219 : ℚ) ^ 2 / 219) <
      433 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 219 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_220 :
    barrierV2 220 ^ 2 / 220 < (71 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 220 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 220 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 220 +
      (4451662 / 100000000) * (-96 / 100) ^ 220 +
      (2545398 / 100000000) * (88 / 100) ^ 220 +
      (-4932634 / 100000000) * (95 / 100) ^ 220 +
      (11618157 / 100000000) * (984 / 1000) ^ 220 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 220 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 220 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 220 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 220 : ℚ) ^ 2 / 220) <
      71 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 220 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_221 :
    barrierV2 221 ^ 2 / 221 < (38 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 221 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 221 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 221 +
      (4451662 / 100000000) * (-96 / 100) ^ 221 +
      (2545398 / 100000000) * (88 / 100) ^ 221 +
      (-4932634 / 100000000) * (95 / 100) ^ 221 +
      (11618157 / 100000000) * (984 / 1000) ^ 221 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 221 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 221 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 221 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 221 : ℚ) ^ 2 / 221) <
      38 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 221 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_222 :
    barrierV2 222 ^ 2 / 222 < (33 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 222 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 222 = (-1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 222 +
      (4451662 / 100000000) * (-96 / 100) ^ 222 +
      (2545398 / 100000000) * (88 / 100) ^ 222 +
      (-4932634 / 100000000) * (95 / 100) ^ 222 +
      (11618157 / 100000000) * (984 / 1000) ^ 222 +
      2 * (-(27238714 / 200000000)) * (78 / 100) ^ 222 +
      2 * (-(-31341084 / 200000000)) * (9 / 10) ^ 222 +
      2 * (-(-6693542 / 200000000)) * (955 / 1000) ^ 222 +
      2 * (-(2055213 / 200000000)) * (984 / 1000) ^ 222 : ℚ) ^ 2 / 222) <
      33 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 222 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    Complex.neg_re, Complex.neg_im, neg_zero,
    mul_zero, mul_neg_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_223 :
    barrierV2 223 ^ 2 / 223 < (374 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 223 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 223 = -Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 223 +
      (4451662 / 100000000) * (-96 / 100) ^ 223 +
      (2545398 / 100000000) * (88 / 100) ^ 223 +
      (-4932634 / 100000000) * (95 / 100) ^ 223 +
      (11618157 / 100000000) * (984 / 1000) ^ 223 +
      2 * (38447936 / 200000000) * (78 / 100) ^ 223 +
      2 * (30188786 / 200000000) * (9 / 10) ^ 223 +
      2 * (-11912254 / 200000000) * (955 / 1000) ^ 223 +
      2 * (21715849 / 200000000) * (984 / 1000) ^ 223 : ℚ) ^ 2 / 223) <
      374 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 223 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    Complex.neg_re, Complex.neg_im, neg_zero, neg_neg,
    mul_zero, mul_neg_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_term_224 :
    barrierV2 224 ^ 2 / 224 < (61 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 224 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 224 = (1 : ℂ) := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 224 +
      (4451662 / 100000000) * (-96 / 100) ^ 224 +
      (2545398 / 100000000) * (88 / 100) ^ 224 +
      (-4932634 / 100000000) * (95 / 100) ^ 224 +
      (11618157 / 100000000) * (984 / 1000) ^ 224 +
      2 * (27238714 / 200000000) * (78 / 100) ^ 224 +
      2 * (-31341084 / 200000000) * (9 / 10) ^ 224 +
      2 * (-6693542 / 200000000) * (955 / 1000) ^ 224 +
      2 * (2055213 / 200000000) * (984 / 1000) ^ 224 : ℚ) ^ 2 / 224) <
      61 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 224 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.one_re, Complex.one_im,
    mul_zero, mul_one, sub_zero, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_224 :
    (∑ k ∈ Finset.range 8,
      barrierV2 (216 + k + 1) ^ 2 / ((216 + k + 1 : ℕ) : ℝ)) ≤
      (1091 / 1000000000 : ℝ) := by
  have h := (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_217.le) barrierV2_norm_term_218.le) barrierV2_norm_term_219.le) barrierV2_norm_term_220.le) barrierV2_norm_term_221.le) barrierV2_norm_term_222.le) barrierV2_norm_term_223.le) barrierV2_norm_term_224.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_224 :
    (∑ k ∈ Finset.range 224,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291645188 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (216 + 8),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_216 barrierV2_norm_block_224
  have hc : (1291644097 / 1000000000 : ℝ) + 1091 / 1000000000 =
      1291645188 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end



noncomputable section
namespace InternalCatalan
open scoped BigOperators

theorem barrierV2_norm_term_225 :
    barrierV2 225 ^ 2 / 225 < (32 / 1000000000 : ℝ) := by
  have hf : barrierFiniteCoeff barrierV2Finite 225 = 0 := by
    norm_num [barrierFiniteCoeff, barrierV2Finite]
  have hi : Complex.I ^ 225 = Complex.I := by
    rw [Complex.I_pow_eq_pow_mod]
    norm_num
  have hq : (((15199211 / 100000000) * (-8 / 10) ^ 225 +
      (4451662 / 100000000) * (-96 / 100) ^ 225 +
      (2545398 / 100000000) * (88 / 100) ^ 225 +
      (-4932634 / 100000000) * (95 / 100) ^ 225 +
      (11618157 / 100000000) * (984 / 1000) ^ 225 +
      2 * (-(38447936 / 200000000)) * (78 / 100) ^ 225 +
      2 * (-(30188786 / 200000000)) * (9 / 10) ^ 225 +
      2 * (-(-11912254 / 200000000)) * (955 / 1000) ^ 225 +
      2 * (-(21715849 / 200000000)) * (984 / 1000) ^ 225 : ℚ) ^ 2 / 225) <
      32 / 1000000000 := by decide +kernel
  rw [barrierV2_eq_coefficientFormula 225 (by norm_num)]
  simp only [barrierV2CoefficientFormula, hf, barrierAxisPhase, hi,
    Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_sub, zero_add]
  simpa only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one] using ((Rat.cast_lt (K := ℝ)).mpr hq)

theorem barrierV2_norm_block_225 :
    (∑ k ∈ Finset.range 1,
      barrierV2 (224 + k + 1) ^ 2 / ((224 + k + 1 : ℕ) : ℝ)) ≤
      (32 / 1000000000 : ℝ) := by
  have h := (add_le_add (le_refl (0 : ℝ)) barrierV2_norm_term_225.le)
  norm_num [Finset.sum_range_succ] at h ⊢
  exact h

theorem barrierV2_norm_prefix_225 :
    (∑ k ∈ Finset.range 225,
      barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤
      (1291645220 / 1000000000 : ℝ) := by
  change (∑ k ∈ Finset.range (224 + 1),
    barrierV2 (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) ≤ _
  rw [Finset.sum_range_add]
  have h := add_le_add barrierV2_norm_prefix_224 barrierV2_norm_block_225
  have hc : (1291645188 / 1000000000 : ℝ) + 32 / 1000000000 =
      1291645220 / 1000000000 := by norm_num
  rw [hc] at h
  exact h

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoNorm
namespace OAI


noncomputable section
namespace InternalCatalan

theorem barrier_case2_norm_rational_upper :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 ≤
      (48651467 / 62500000 : ℝ) := by
  have hp : barrierTrialNormSq barrierP2 ≤
      (66295876 / 1000000000 : ℝ) + 154 / 100000000 := by
    refine (barrierTrialNormSq_le_prefix_add_geometric_tail barrierP2 60
      (94 / 100) (33 / 10000) barrier_trials_norm_summable.1
      (by norm_num) (by norm_num) (by norm_num) barrierP2_tail_decay).trans ?_
    exact add_le_add barrierP2_norm_prefix_60 (by norm_num)
  have hv : barrierTrialNormSq barrierV2 ≤
      (1291645220 / 1000000000 : ℝ) + 1206 / 100000000 := by
    refine (barrierTrialNormSq_le_prefix_add_geometric_tail barrierV2 225
      (984 / 1000) (93 / 10000) barrier_trials_norm_summable.2.1
      (by norm_num) (by norm_num) (by norm_num) barrierV2_tail_decay).trans ?_
    exact add_le_add barrierV2_norm_prefix_225 (by norm_num)
  calc
    _ ≤ 2 * ((66295876 / 1000000000 : ℝ) + 154 / 100000000) +
        (1 / 2 : ℝ) * ((1291645220 / 1000000000 : ℝ) + 1206 / 100000000) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hp (by norm_num))
        (mul_le_mul_of_nonneg_left hv (by norm_num))
    _ = _ := by norm_num


end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan

theorem solution :
    2 * barrierTrialNormSq barrierP2 + (1 / 2 : ℝ) * barrierTrialNormSq barrierV2 ≤
      (48651467 / 62500000 : ℝ) := by
  first
  | exact @OAI.InternalCatalan.barrier_case2_norm_rational_upper
  | (apply OAI.InternalCatalan.barrier_case2_norm_rational_upper <;> assumption)

end

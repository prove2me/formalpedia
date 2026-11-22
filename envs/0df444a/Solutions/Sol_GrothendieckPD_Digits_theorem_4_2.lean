-- Prove2me | solution 1 for GrothendieckPD.Digits.theorem_4_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:54:18.254617+00:00
-- url     : https://prove2.me/submissions/30790bfd-bfd1-4c7e-bf91-1101072a46b9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_RoundingScheme
import Theorems.Thm_GrothendieckPD_Digits_lemma_2_1
import Theorems.Thm_GrothendieckPD_Digits_lemma_3_3
import Theorems.Thm_GrothendieckPD_Digits_lemma_C_1
import Theorems.Thm_GrothendieckPD_Digits_lemma_C_2
import Theorems.Thm_GrothendieckPD_Digits_lemma_C_3
import Theorems.Thm_GrothendieckPD_Digits_lemma_C_4

open MeasureTheory ProbabilityTheory GrothendieckPD.Digits

namespace GrothendieckPDTheorem42Aux

/-! ### 1. Basic numerical and structural facts about `lam` and `pcoef` -/

private lemma lam_nonneg (i : ℕ) : 0 ≤ lam i := by
  unfold lam
  split <;> norm_num

private lemma sum_lam : ∑ i ∈ Finset.range 32, lam i = 1 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, lam]
  norm_num

private lemma pcoef_eq_zero_of_even (i m : ℕ) (hm : Even m) : pcoef i m = 0 := by
  obtain ⟨k, rfl⟩ := hm
  unfold pcoef
  split <;> first | rfl | omega

private lemma pcoef_pivot_ne_zero (i : ℕ) (hi : i < 32) (hi14 : i ≠ 14) :
    pcoef i (if i = 1 then 3 else 1) ≠ 0 := by
  interval_cases i
  all_goals
    first
    | exact absurd rfl hi14
    | norm_num [pcoef]

private lemma sum_range_32_partition (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range 32, g i =
      g 14 + (∑ i ∈ Finset.Icc 17 31, g i) +
        (∑ i ∈ Finset.Icc 1 13, g i) + (∑ i ∈ ({0, 15, 16} : Finset ℕ), g i) := by
  have h1 : Finset.range 32 =
      (insert 14 (Finset.Icc 17 31) ∪ Finset.Icc 1 13) ∪ ({0, 15, 16} : Finset ℕ) := by decide
  have hd1 : Disjoint (insert 14 (Finset.Icc 17 31) ∪ Finset.Icc 1 13)
      ({0, 15, 16} : Finset ℕ) := by decide
  have hd2 : Disjoint (insert 14 (Finset.Icc 17 31)) (Finset.Icc 1 13) := by decide
  have h14 : (14 : ℕ) ∉ Finset.Icc 17 31 := by decide
  rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_insert h14]

/-! ### 2. Summability and numerical bound on `cMix` from Lemmas C.1–C.4 -/

private noncomputable def tailBound (k : ℕ) : ℝ :=
  lam 14 * |Hcoef 14 (k + 682)| +
    (∑ i ∈ Finset.Icc 17 31, lam i * |Hcoef i (k + 682)|) +
    (∑ i ∈ Finset.Icc 1 13, lam i * |Hcoef i (k + 682)|) +
    |∑ i ∈ ({0, 15, 16} : Finset ℕ), lam i * Hcoef i (k + 682)|

private lemma abs_cMix_tail_le (k : ℕ) : |cMix (k + 682)| ≤ tailBound k := by
  unfold cMix tailBound
  rw [sum_range_32_partition]
  have htri1 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
    calc |a + b + c + d| ≤ |a + b + c| + |d| := abs_add_le _ _
      _ ≤ |a + b| + |c| + |d| := by linarith [abs_add_le (a + b) c]
      _ ≤ |a| + |b| + |c| + |d| := by linarith [abs_add_le a b]
  have h14 : |lam 14 * Hcoef 14 (k + 682)| = lam 14 * |Hcoef 14 (k + 682)| := by
    rw [abs_mul, abs_of_nonneg (lam_nonneg 14)]
  have h17 : |∑ i ∈ Finset.Icc 17 31, lam i * Hcoef i (k + 682)| ≤
      ∑ i ∈ Finset.Icc 17 31, lam i * |Hcoef i (k + 682)| := by
    calc |∑ i ∈ Finset.Icc 17 31, lam i * Hcoef i (k + 682)|
        ≤ ∑ i ∈ Finset.Icc 17 31, |lam i * Hcoef i (k + 682)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Icc 17 31, lam i * |Hcoef i (k + 682)| :=
          Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (lam_nonneg i)]
  have h1 : |∑ i ∈ Finset.Icc 1 13, lam i * Hcoef i (k + 682)| ≤
      ∑ i ∈ Finset.Icc 1 13, lam i * |Hcoef i (k + 682)| := by
    calc |∑ i ∈ Finset.Icc 1 13, lam i * Hcoef i (k + 682)|
        ≤ ∑ i ∈ Finset.Icc 1 13, |lam i * Hcoef i (k + 682)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.Icc 1 13, lam i * |Hcoef i (k + 682)| :=
          Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (lam_nonneg i)]
  have := htri1 (lam 14 * Hcoef 14 (k + 682))
    (∑ i ∈ Finset.Icc 17 31, lam i * Hcoef i (k + 682))
    (∑ i ∈ Finset.Icc 1 13, lam i * Hcoef i (k + 682))
    (∑ i ∈ ({0, 15, 16} : Finset ℕ), lam i * Hcoef i (k + 682))
  linarith

private lemma summable_tailBound : Summable tailBound := by
  have hC2 := lemma_C_2.1
  have hC3 := lemma_C_3.1
  have hC4 := lemma_C_4.1
  have hs14 : Summable fun k => lam 14 * |Hcoef 14 (k + 682)| :=
    (hC2 14 (by simp)).mul_left (lam 14)
  have hs17 : Summable fun k => ∑ i ∈ Finset.Icc 17 31, lam i * |Hcoef i (k + 682)| :=
    summable_sum fun i hi => (hC2 i (Finset.mem_insert_of_mem hi)).mul_left (lam i)
  have hs1 : Summable fun k => ∑ i ∈ Finset.Icc 1 13, lam i * |Hcoef i (k + 682)| :=
    summable_sum fun i hi => (hC3 i hi).mul_left (lam i)
  exact ((hs14.add hs17).add hs1).add hC4

private lemma summable_abs_cMix_tail : Summable fun k => |cMix (k + 682)| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) abs_cMix_tail_le summable_tailBound

private lemma summable_abs_cMix : Summable fun m => |cMix m| :=
  (summable_nat_add_iff 682).mp summable_abs_cMix_tail

private lemma summable_abs_cMix_odd : Summable fun k => |cMix (2 * k + 3)| :=
  summable_abs_cMix.comp_injective (fun _ _ h => by omega)

private lemma tsum_abs_cMix_tail_lt :
    ∑' k, |cMix (k + 682)| < (0.000045850994870209 : ℝ) := by
  have hC2 := lemma_C_2
  have hC3 := lemma_C_3
  have hC4 := lemma_C_4
  have hs14 : Summable fun k => lam 14 * |Hcoef 14 (k + 682)| :=
    (hC2.1 14 (by simp)).mul_left (lam 14)
  have hs17_i : ∀ i ∈ Finset.Icc 17 31, Summable fun k => lam i * |Hcoef i (k + 682)| :=
    fun i hi => (hC2.1 i (Finset.mem_insert_of_mem hi)).mul_left (lam i)
  have hs17 : Summable fun k => ∑ i ∈ Finset.Icc 17 31, lam i * |Hcoef i (k + 682)| :=
    summable_sum hs17_i
  have hs1_i : ∀ i ∈ Finset.Icc 1 13, Summable fun k => lam i * |Hcoef i (k + 682)| :=
    fun i hi => (hC3.1 i hi).mul_left (lam i)
  have hs1 : Summable fun k => ∑ i ∈ Finset.Icc 1 13, lam i * |Hcoef i (k + 682)| :=
    summable_sum hs1_i
  have hle : ∑' k, |cMix (k + 682)| ≤ ∑' k, tailBound k :=
    summable_abs_cMix_tail.tsum_le_tsum abs_cMix_tail_le summable_tailBound
  have heq : ∑' k, tailBound k =
      (lam 14 * ∑' k, |Hcoef 14 (k + 682)| +
        ∑ i ∈ Finset.Icc 17 31, lam i * ∑' k, |Hcoef i (k + 682)|) +
      (∑ i ∈ Finset.Icc 1 13, lam i * ∑' k, |Hcoef i (k + 682)|) +
      ∑' k, |∑ i ∈ ({0, 15, 16} : Finset ℕ), lam i * Hcoef i (k + 682)| := by
    unfold tailBound
    rw [((hs14.add hs17).add hs1).tsum_add hC4.1,
      (hs14.add hs17).tsum_add hs1, hs14.tsum_add hs17,
      tsum_mul_left, Summable.tsum_finsetSum hs17_i, Summable.tsum_finsetSum hs1_i]
    congr 2
    · congr 1
      exact Finset.sum_congr rfl fun i _ => tsum_mul_left
    · exact Finset.sum_congr rfl fun i _ => tsum_mul_left
  linarith [hC2.2, hC3.2, hC4.2]

private lemma sum_Icc_two_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ m ∈ Finset.Icc 2 (N + 1), f m = ∑ m ∈ Finset.range N, f (m + 2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h : Finset.Icc 2 (n + 1 + 1) = insert (n + 2) (Finset.Icc 2 (n + 1)) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [h, Finset.sum_insert (by simp), add_comm]

private lemma krivineValue_cMix_gt :
    (0.561831528950464991 : ℝ) < cMix 1 - ∑' k, |cMix (2 * k + 3)| := by
  have hs2 : Summable fun m => |cMix (m + 2)| := (summable_nat_add_iff 2).mpr summable_abs_cMix
  have hodd_le : ∑' k, |cMix (2 * k + 3)| ≤ ∑' m, |cMix (m + 2)| := by
    have hcomp := tsum_comp_le_tsum_of_inj hs2 (fun _ => abs_nonneg _)
      (i := fun k : ℕ => 2 * k + 1) (fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega)
    simpa [Function.comp_def, Nat.add_assoc] using hcomp
  have hsplit : ∑' m, |cMix (m + 2)| =
      (∑ m ∈ Finset.Icc 2 681, |cMix m|) + ∑' k, |cMix (k + 682)| := by
    have h := hs2.sum_add_tsum_nat_add 680
    rw [← h, sum_Icc_two_eq_sum_range (fun m => |cMix m|) 680]
  linarith [lemma_C_1, tsum_abs_cMix_tail_lt]

/-! ### 3. Measurability, Boolean-valuedness, and oddness of the rounding functions -/

private lemma measurable_sgn : Measurable sgn :=
  Measurable.ite measurableSet_Ici measurable_const measurable_const

private lemma sgn_eq_one_or_neg_one (x : ℝ) : sgn x = 1 ∨ sgn x = -1 := by
  unfold sgn; split_ifs <;> simp

private lemma sgn_neg_of_ne_zero {x : ℝ} (hx : x ≠ 0) : sgn (-x) = -sgn x := by
  unfold sgn
  rcases lt_or_gt_of_ne hx with h | h
  · rw [if_pos (by linarith), if_neg (by linarith)]; ring
  · rw [if_neg (by linarith), if_pos (by linarith)]

private lemma measurable_psi (k : ℕ) : Measurable (psi k) := by
  unfold psi
  have hcont : Continuous fun s : ℝ => Polynomial.aeval s (Polynomial.hermite k) := by
    simpa [Polynomial.aeval_def, ← Polynomial.eval_map] using
      ((Polynomial.hermite k).map (Int.castRingHom ℝ)).continuous
  exact (hcont.div_const _).measurable

private lemma measurable_rfun : Measurable rfun := by
  unfold rfun
  exact (((((((measurable_const.mul (measurable_psi 1)).sub
    (measurable_const.mul (measurable_psi 3))).sub
    (measurable_const.mul (measurable_psi 5))).sub
    (measurable_const.mul (measurable_psi 7))).add
    (measurable_const.mul (measurable_psi 9))).add
    (measurable_const.mul (measurable_psi 11))).sub
    (measurable_const.mul (measurable_psi 13))).add
    (measurable_const.mul (measurable_psi 15))

private lemma hermite_aeval_neg (n : ℕ) (s : ℝ) :
    Polynomial.aeval (-s) (Polynomial.hermite n) =
      (-1 : ℝ) ^ n * Polynomial.aeval s (Polynomial.hermite n) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range,
    Polynomial.eval₂_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hpar : Odd (n + k)
  · rw [Polynomial.coeff_hermite_of_odd_add hpar]
    simp
  · have hev : Even (n + k) := Nat.not_odd_iff_even.mp hpar
    obtain ⟨m, hm⟩ := hev
    have hpow : (-1 : ℝ) ^ k = (-1 : ℝ) ^ n := by
      have h1 : (-1 : ℝ) ^ (n + k) = 1 := by
        rw [hm, ← two_mul, pow_mul]; norm_num
      have h2 : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      calc (-1 : ℝ) ^ k = 1 * (-1 : ℝ) ^ k := (one_mul _).symm
        _ = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) * (-1 : ℝ) ^ k := by rw [h2]
        _ = (-1 : ℝ) ^ n * ((-1 : ℝ) ^ (n + k)) := by rw [pow_add, mul_assoc]
        _ = (-1 : ℝ) ^ n := by rw [h1, mul_one]
    have hneg : (-s) ^ k = (-1 : ℝ) ^ n * s ^ k := by
      rw [neg_eq_neg_one_mul, mul_pow, hpow]
    rw [hneg]
    ring

private lemma psi_neg_of_odd {k : ℕ} (hk : Odd k) (s : ℝ) : psi k (-s) = -psi k s := by
  unfold psi
  rw [hermite_aeval_neg, hk.neg_one_pow]
  ring

private lemma rfun_neg (s : ℝ) : rfun (-s) = -rfun s := by
  unfold rfun
  rw [psi_neg_of_odd (by decide : Odd 1), psi_neg_of_odd (by decide : Odd 3),
    psi_neg_of_odd (by decide : Odd 5), psi_neg_of_odd (by decide : Odd 7),
    psi_neg_of_odd (by decide : Odd 9), psi_neg_of_odd (by decide : Odd 11),
    psi_neg_of_odd (by decide : Odd 13), psi_neg_of_odd (by decide : Odd 15)]
  ring

private lemma measurable_list_sum_mapIdx (L : List ℝ) (s : ℕ) :
    Measurable fun x : ℝ =>
      (L.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + s) else 0).sum := by
  induction L generalizing s with
  | nil =>
    simp [measurable_const]
  | cons a tl ih =>
    have hstep : ∀ x : ℝ,
        ((a :: tl).mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + s) else 0).sum =
        (if a ≤ x then (-1 : ℝ) ^ s else 0) +
        (tl.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + (s + 1)) else 0).sum := by
      intro x
      simp only [List.mapIdx_cons, List.sum_cons, zero_add]
      congr 2
      ext idx r
      simp [Nat.add_assoc, Nat.add_comm 1 s]
    simp_rw [hstep]
    refine Measurable.add ?_ (ih (s + 1))
    exact Measurable.ite measurableSet_Ici measurable_const measurable_const

private lemma measurable_stairValue (k : ℕ) : Measurable (stairValue k) := by
  unfold stairValue
  exact measurable_const.add (measurable_const.mul (measurable_list_sum_mapIdx (breakpoints k) 1))

private lemma measurable_stairValue_uncurry : Measurable (Function.uncurry stairValue) :=
  measurable_from_prod_countable_right fun k => measurable_stairValue k

private lemma measurable_FstarNonneg : Measurable (Function.uncurry FstarNonneg) := by
  have h1 : Measurable fun p : ℝ × ℝ => FstarNonneg p.1 p.2 := by
    unfold FstarNonneg
    refine Measurable.ite (measurable_snd measurableSet_Ici) ?_ ?_
    · exact (measurable_sgn.comp measurable_fst).neg
    · have hfloor : Measurable fun p : ℝ × ℝ => ⌊256 * p.2⌋₊ :=
        Nat.measurable_floor.comp (measurable_const.mul measurable_snd)
      exact measurable_stairValue_uncurry.comp (hfloor.prodMk measurable_fst)
  exact h1

private lemma measurable_Fstar : Measurable (Function.uncurry Fstar) := by
  have h1 : Measurable fun p : ℝ × ℝ => Fstar p.1 p.2 := by
    unfold Fstar
    refine Measurable.ite (measurable_snd measurableSet_Ici) measurable_FstarNonneg ?_
    exact (measurable_FstarNonneg.comp (measurable_fst.neg.prodMk measurable_snd.neg)).neg
  exact h1

private lemma alternating_prefix_sum (L : List ℝ) (hL : L.Pairwise (· ≤ ·)) (x : ℝ) (s : ℕ) :
    (L.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + s) else 0).sum = 0 ∨
    (L.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + s) else 0).sum = (-1 : ℝ) ^ s := by
  induction L generalizing s with
  | nil => left; simp
  | cons a tl ih =>
    rw [List.pairwise_cons] at hL
    have hstep :
        ((a :: tl).mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + s) else 0).sum =
        (if a ≤ x then (-1 : ℝ) ^ s else 0) +
        (tl.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + (s + 1)) else 0).sum := by
      simp only [List.mapIdx_cons, List.sum_cons, zero_add]
      congr 2
      ext idx r
      simp [Nat.add_assoc, Nat.add_comm 1 s]
    rw [hstep]
    by_cases hax : a ≤ x
    · rw [if_pos hax]
      rcases ih hL.2 (s + 1) with h0 | h1
      · right; rw [h0, add_zero]
      · left; rw [h1, pow_succ]; ring
    · left
      rw [if_neg hax, zero_add]
      have hzero : ∀ t ∈ (tl.mapIdx fun idx r => if r ≤ x then (-1 : ℝ) ^ (idx + (s + 1)) else 0),
          t = 0 := by
        intro t ht
        rw [List.mem_mapIdx] at ht
        rcases ht with ⟨idx, hidx, rfl⟩
        have har : a ≤ tl[idx] := hL.1 _ (List.getElem_mem hidx)
        rw [if_neg (fun h => hax (har.trans h))]
      exact List.sum_eq_zero hzero

private lemma stairValue_eq_one_or_neg_one (k : ℕ) (x : ℝ) :
    stairValue k x = 1 ∨ stairValue k x = -1 := by
  unfold stairValue
  have hsorted : (breakpoints k).Pairwise (· ≤ ·) := Multiset.pairwise_sort _ _
  rcases alternating_prefix_sum (breakpoints k) hsorted x 1 with h0 | h1
  · left; rw [h0]; ring
  · right; rw [h1]; norm_num

private lemma FstarNonneg_eq_one_or_neg_one (x y : ℝ) :
    FstarNonneg x y = 1 ∨ FstarNonneg x y = -1 := by
  unfold FstarNonneg
  split_ifs
  · rcases sgn_eq_one_or_neg_one x with h | h <;> [right; left] <;> linarith
  · exact stairValue_eq_one_or_neg_one _ x

private lemma Fstar_eq_one_or_neg_one (x y : ℝ) : Fstar x y = 1 ∨ Fstar x y = -1 := by
  unfold Fstar
  split_ifs
  · exact FstarNonneg_eq_one_or_neg_one x y
  · rcases FstarNonneg_eq_one_or_neg_one (-x) (-y) with h | h <;> [right; left] <;> linarith

private lemma Fstar_neg_neg {x y : ℝ} (hy : y ≠ 0) : Fstar (-x) (-y) = -Fstar x y := by
  unfold Fstar
  rcases lt_or_gt_of_ne hy with h | h
  · rw [if_pos (by linarith), if_neg (by linarith), neg_neg]
  · rw [if_neg (by linarith), if_pos (by linarith), neg_neg, neg_neg]

private lemma measurable_Wfun (i : ℕ) : Measurable (Wfun i) := by
  unfold Wfun
  refine Measurable.add ?_ (measurable_const.mul (measurable_pi_apply _))
  exact Finset.measurable_sum _ fun m _ => measurable_const.mul (measurable_pi_apply _)

private lemma measurable_Wfun' (i : ℕ) : Measurable (Wfun' i) := by
  unfold Wfun'
  refine Measurable.add ?_ (measurable_const.mul (measurable_pi_apply _))
  exact Finset.measurable_sum _ fun m _ => measurable_const.mul (measurable_pi_apply _)

private lemma measurable_roundF (i : ℕ) : Measurable (roundF i) := by
  unfold roundF
  by_cases hi14 : i = 14
  · simp only [hi14, ↓reduceIte]
    exact measurable_Fstar.comp (f := fun x : GPoint => (x (gradeVar 3), x (gradeVar 5)))
      ((measurable_pi_apply (gradeVar 3)).prodMk (measurable_pi_apply (gradeVar 5)))
  · by_cases hi17 : 17 ≤ i
    · simp only [hi14, ↓reduceIte, hi17]
      exact measurable_sgn.comp (measurable_Wfun i)
    · simp only [hi14, ↓reduceIte, hi17]
      unfold Fgraph
      exact measurable_sgn.comp ((measurable_Wfun i).add
        (((measurable_rfun.comp (measurable_pi_apply _)).add
          (measurable_rfun.comp (measurable_pi_apply _))).add
          (measurable_rfun.comp (measurable_pi_apply _))))

private lemma measurable_roundG (i : ℕ) : Measurable (roundG i) := by
  unfold roundG
  by_cases hi14 : i = 14
  · simp only [hi14, ↓reduceIte]
    exact measurable_Fstar.comp (f := fun x : GPoint => (-x (gradeVar 3), x (gradeVar 5)))
      (((measurable_pi_apply (gradeVar 3)).neg).prodMk (measurable_pi_apply (gradeVar 5)))
  · by_cases hi17 : 17 ≤ i
    · simp only [hi14, ↓reduceIte, hi17]
      exact measurable_sgn.comp (measurable_Wfun' i)
    · simp only [hi14, ↓reduceIte, hi17]
      unfold Fgraph
      exact measurable_sgn.comp ((measurable_Wfun' i).add
        (((measurable_rfun.comp (measurable_pi_apply _).neg).add
          (measurable_rfun.comp (measurable_pi_apply _).neg)).add
          (measurable_rfun.comp (measurable_pi_apply _).neg)))

private lemma roundF_eq_one_or_neg_one (i : ℕ) (x : GPoint) :
    roundF i x = 1 ∨ roundF i x = -1 := by
  unfold roundF
  split_ifs
  · exact Fstar_eq_one_or_neg_one _ _
  · exact sgn_eq_one_or_neg_one _
  · exact sgn_eq_one_or_neg_one _

private lemma roundG_eq_one_or_neg_one (i : ℕ) (x : GPoint) :
    roundG i x = 1 ∨ roundG i x = -1 := by
  unfold roundG
  split_ifs
  · exact Fstar_eq_one_or_neg_one _ _
  · exact sgn_eq_one_or_neg_one _
  · exact sgn_eq_one_or_neg_one _

private instance : IsProbabilityMeasure gradedGaussian := by
  unfold gradedGaussian; infer_instance

private lemma isAsympBoolean_of_measurable_pm {f : GPoint → ℝ} (hm : Measurable f)
    (hb : ∀ x, f x = 1 ∨ f x = -1) : IsAsympBoolean f := by
  refine ⟨?_, Filter.Eventually.of_forall hb⟩
  refine MemLp.of_bound hm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
  rcases hb x with h | h <;> simp [h]

private lemma isAsympBoolean_roundF (i : ℕ) : IsAsympBoolean (roundF i) :=
  isAsympBoolean_of_measurable_pm (measurable_roundF i) (roundF_eq_one_or_neg_one i)

private lemma isAsympBoolean_roundG (i : ℕ) : IsAsympBoolean (roundG i) :=
  isAsympBoolean_of_measurable_pm (measurable_roundG i) (roundG_eq_one_or_neg_one i)

private lemma gradedFlip_gradeVar {m : ℕ} (hm : 1 ≤ m) (hodd : Odd m) (x : GPoint) :
    gradedFlip x (gradeVar m) = -x (gradeVar m) := by
  unfold gradedFlip gradeVar
  have hval : (m.toPNat' : ℕ) = m := by
    cases m with
    | zero => omega
    | succ k => rfl
  rw [hval, hodd.neg_one_pow, neg_one_mul]

private lemma gradedFlip_g1 (j : ℕ) (x : GPoint) :
    gradedFlip x (g1 j) = -x (g1 j) := by
  unfold gradedFlip g1
  simp

private lemma Wfun_gradedFlip (i : ℕ) (x : GPoint) : Wfun i (gradedFlip x) = -Wfun i x := by
  unfold Wfun
  rw [gradedFlip_g1, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [tableDegrees, Finset.mem_Icc] at hm
    rcases Nat.even_or_odd m with hev | hodd
    · rw [pcoef_eq_zero_of_even i m hev]; simp
    · rw [gradedFlip_gradeVar hm.1 hodd]; ring
  · ring

private lemma Wfun'_gradedFlip (i : ℕ) (x : GPoint) : Wfun' i (gradedFlip x) = -Wfun' i x := by
  unfold Wfun'
  rw [gradedFlip_g1, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp only [tableDegrees, Finset.mem_Icc] at hm
    rcases Nat.even_or_odd m with hev | hodd
    · rw [pcoef_eq_zero_of_even i m hev]; simp
    · rw [gradedFlip_gradeVar hm.1 hodd]; ring
  · ring

/-! ### 4. Null-set lemmas on `gradedGaussian` and oddness of `roundF`, `roundG` -/

private lemma ae_coord_ne_zero (v : GVar) : ∀ᵐ x ∂gradedGaussian, x v ≠ 0 := by
  rw [ae_iff]
  have hset : {x : GPoint | ¬ x v ≠ 0} = (fun x : GPoint => x v) ⁻¹' ({0} : Set ℝ) := by
    ext x; simp
  rw [hset]
  have hmp : MeasurePreserving (fun x : GPoint => x v) gradedGaussian (gaussianReal 0 1) :=
    measurePreserving_eval_infinitePi (fun _ : GVar => gaussianReal 0 1) v
  rw [hmp.measure_preimage (MeasurableSet.singleton 0).nullMeasurableSet]
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  exact measure_singleton 0

private lemma ae_linear_add_ne_zero (I : Finset GVar) (v : GVar) (hv : v ∈ I)
    (c : ℝ) (hc : c ≠ 0) (h : ({w : I // w ≠ ⟨v, hv⟩} → ℝ) → ℝ) (hh : Measurable h) :
    ∀ᵐ x ∂gradedGaussian, c * x v + h (fun w => x w.1.1) ≠ 0 := by
  rw [ae_iff]
  let p : I → Prop := fun w => w = ⟨v, hv⟩
  let e1 : (I → ℝ) ≃ᵐ ({w : I // p w} → ℝ) × ({w : I // ¬p w} → ℝ) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => ℝ) p
  let _ : Unique {w : I // p w} := ⟨⟨⟨⟨v, hv⟩, rfl⟩⟩, fun ⟨w, hw⟩ => Subtype.ext hw⟩
  let e2 : ({w : I // p w} → ℝ) × ({w : I // ¬p w} → ℝ) ≃ᵐ ℝ × ({w : I // ¬p w} → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique (fun _ : {w : I // p w} => ℝ))
      (MeasurableEquiv.refl _)
  let e : (I → ℝ) ≃ᵐ ℝ × ({w : I // ¬p w} → ℝ) := e1.trans e2
  let μI : Measure (I → ℝ) := Measure.pi (fun _ : I => gaussianReal 0 1)
  let μR : Measure ({w : I // ¬p w} → ℝ) := Measure.pi (fun _ : {w : I // ¬p w} => gaussianReal 0 1)
  have hmp1 := measurePreserving_piEquivPiSubtypeProd (fun _ : I => gaussianReal 0 1) p
  have hmp2 : MeasurePreserving e2
      ((@Measure.pi {w : I // p w} (fun _ => ℝ) (Subtype.fintype p) _
          (fun _ => gaussianReal 0 1)).prod μR)
      ((gaussianReal 0 1).prod μR) := by
    have hft : Subtype.fintype p = Unique.fintype := Subsingleton.elim _ _
    rw [hft]
    exact (measurePreserving_piUnique (fun _ : {w : I // p w} => gaussianReal 0 1)).prod
      (MeasurePreserving.id μR)
  have hmp_e : MeasurePreserving e μI ((gaussianReal 0 1).prod μR) := hmp2.comp hmp1
  have hmp_r : MeasurePreserving I.restrict gradedGaussian μI :=
    ⟨Finset.measurable_restrict I,
      Measure.infinitePi_map_restrict (fun _ : GVar => gaussianReal 0 1)⟩
  have hmp : MeasurePreserving (e ∘ I.restrict) gradedGaussian ((gaussianReal 0 1).prod μR) :=
    hmp_e.comp hmp_r
  let S : Set (ℝ × ({w : I // ¬p w} → ℝ)) := {q | c * q.1 + h q.2 = 0}
  have hSm : MeasurableSet S := by
    have hm : Measurable fun q : ℝ × ({w : I // ¬p w} → ℝ) => c * q.1 + h q.2 :=
      (measurable_const.mul measurable_fst).add (hh.comp measurable_snd)
    exact hm (MeasurableSet.singleton 0)
  have hpre : {x : GPoint | ¬ c * x v + h (fun w => x w.1.1) ≠ 0} = (e ∘ I.restrict) ⁻¹' S := by
    ext x
    change (¬ c * x v + h (fun w => x w.1.1) ≠ 0) ↔
      c * (e (I.restrict x)).1 + h (e (I.restrict x)).2 = 0
    have h1 : (e (I.restrict x)).1 = x v := rfl
    have h2 : (e (I.restrict x)).2 = fun w => x w.1.1 := rfl
    rw [h1, h2, not_not]
  rw [hpre, hmp.measure_preimage hSm.nullMeasurableSet]
  rw [Measure.prod_apply_symm hSm]
  have : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  have hslice : ∀ b : {w : I // ¬p w} → ℝ,
      gaussianReal 0 1 ((fun a => (a, b)) ⁻¹' S) = 0 := by
    intro b
    have hEq : ((fun a => (a, b)) ⁻¹' S) = {-h b / c} := by
      ext a
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff, S]
      constructor
      · intro ha
        exact eq_div_of_mul_eq hc (by linarith)
      · intro ha
        rw [ha, mul_div_cancel₀ _ hc]
        ring
    rw [hEq]
    exact measure_singleton _
  simp [hslice]

private def usedVars : Finset GVar :=
  (tableDegrees.image gradeVar) ∪ {g1 2, g1 3, g1 4, g1 5, g1 6}

private lemma gradeVar_mem_usedVars {m : ℕ} (hm : m ∈ tableDegrees) : gradeVar m ∈ usedVars :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm)

private lemma g1_mem_usedVars (j : ℕ) (hj : j ∈ ({2, 3, 4, 5, 6} : Finset ℕ)) :
    g1 j ∈ usedVars := by
  refine Finset.mem_union_right _ ?_
  fin_cases hj <;> simp

private lemma gradeVar_ne_g1 (m j : ℕ) (hj : j ≠ 1) : gradeVar m ≠ g1 j := by
  intro h
  have := congrArg Prod.snd h
  exact hj this.symm

private lemma gradeVar_injOn {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : gradeVar m = gradeVar n) : m = n := by
  have h1 := congrArg (fun p : GVar => (p.1 : ℕ)) h
  unfold gradeVar at h1
  cases m with
  | zero => omega
  | succ a =>
    cases n with
    | zero => omega
    | succ b => exact h1

private lemma ae_Wfun_add_ne_zero (i : ℕ) (hi : i < 32) (hi14 : i ≠ 14)
    (extra : GPoint → ℝ)
    (h_extra : ∃ g : ({w : usedVars // w ≠ ⟨gradeVar (if i = 1 then 3 else 1),
      gradeVar_mem_usedVars (by split_ifs <;> decide)⟩} → ℝ) → ℝ,
      Measurable g ∧ ∀ x, extra x = g (fun w => x w.1.1)) :
    ∀ᵐ x ∂gradedGaussian, Wfun i x + extra x ≠ 0 := by
  let m0 : ℕ := if i = 1 then 3 else 1
  have hm0 : m0 ∈ tableDegrees := by
    dsimp only [m0]; split_ifs <;> decide
  have hm0_pos : 1 ≤ m0 := (Finset.mem_Icc.mp hm0).1
  let v0 : GVar := gradeVar m0
  have hv0 : v0 ∈ usedVars := gradeVar_mem_usedVars hm0
  let v0' : usedVars := ⟨v0, hv0⟩
  have hpne : pcoef i m0 ≠ 0 := pcoef_pivot_ne_zero i hi hi14
  have hcne : Real.sqrt |pcoef i m0| ≠ 0 :=
    (Real.sqrt_pos.mpr (abs_pos.mpr hpne)).ne'
  obtain ⟨g, hg_meas, hg_eq⟩ := h_extra
  let rest : ({w : usedVars // w ≠ v0'} → ℝ) → ℝ := fun y =>
    (∑ m ∈ (tableDegrees.erase m0).attach,
      Real.sqrt |pcoef i m.1| *
        y ⟨⟨gradeVar m.1, gradeVar_mem_usedVars (Finset.mem_of_mem_erase m.2)⟩, by
          intro heq
          have hgv : gradeVar m.1 = gradeVar m0 := congrArg Subtype.val heq
          have hm1 : 1 ≤ m.1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase m.2)).1
          exact (Finset.mem_erase.mp m.2).1 (gradeVar_injOn hm1 hm0_pos hgv)⟩) +
    Real.sqrt (1 - ∑ m ∈ tableDegrees, |pcoef i m|) *
      y ⟨⟨g1 2, g1_mem_usedVars 2 (by decide)⟩, by
        intro heq
        exact (gradeVar_ne_g1 m0 2 (by decide)) (congrArg Subtype.val heq).symm⟩ +
    g y
  have hrest_meas : Measurable rest := by
    dsimp only [rest]
    refine Measurable.add (Measurable.add ?_ ?_) hg_meas
    · exact Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_pi_apply _)
    · exact measurable_const.mul (measurable_pi_apply _)
  have hsplit : ∀ x : GPoint,
      Wfun i x + extra x = Real.sqrt |pcoef i m0| * x v0 + rest (fun w => x w.1.1) := by
    intro x
    unfold Wfun
    rw [← Finset.add_sum_erase _ _ hm0, hg_eq x]
    have hsum : ∑ m ∈ tableDegrees.erase m0, Real.sqrt |pcoef i m| * x (gradeVar m) =
        ∑ m ∈ (tableDegrees.erase m0).attach, Real.sqrt |pcoef i m.1| * x (gradeVar m.1) :=
      (Finset.sum_attach (tableDegrees.erase m0) fun m =>
        Real.sqrt |pcoef i m| * x (gradeVar m)).symm
    dsimp only [rest]
    rw [hsum]
    ring
  simpa only [hsplit] using ae_linear_add_ne_zero usedVars v0 hv0 _ hcne rest hrest_meas

private lemma ae_Wfun'_add_ne_zero (i : ℕ) (hi : i < 32) (hi14 : i ≠ 14)
    (extra : GPoint → ℝ)
    (h_extra : ∃ g : ({w : usedVars // w ≠ ⟨gradeVar (if i = 1 then 3 else 1),
      gradeVar_mem_usedVars (by split_ifs <;> decide)⟩} → ℝ) → ℝ,
      Measurable g ∧ ∀ x, extra x = g (fun w => x w.1.1)) :
    ∀ᵐ x ∂gradedGaussian, Wfun' i x + extra x ≠ 0 := by
  let m0 : ℕ := if i = 1 then 3 else 1
  have hm0 : m0 ∈ tableDegrees := by
    dsimp only [m0]; split_ifs <;> decide
  have hm0_pos : 1 ≤ m0 := (Finset.mem_Icc.mp hm0).1
  let v0 : GVar := gradeVar m0
  have hv0 : v0 ∈ usedVars := gradeVar_mem_usedVars hm0
  let v0' : usedVars := ⟨v0, hv0⟩
  have hpne : pcoef i m0 ≠ 0 := pcoef_pivot_ne_zero i hi hi14
  have hsgn_ne : sgn (pcoef i m0) ≠ 0 := by
    rcases sgn_eq_one_or_neg_one (pcoef i m0) with h | h <;> simp [h]
  have hcne : sgn (pcoef i m0) * Real.sqrt |pcoef i m0| ≠ 0 :=
    mul_ne_zero hsgn_ne (Real.sqrt_pos.mpr (abs_pos.mpr hpne)).ne'
  obtain ⟨g, hg_meas, hg_eq⟩ := h_extra
  let rest : ({w : usedVars // w ≠ v0'} → ℝ) → ℝ := fun y =>
    (∑ m ∈ (tableDegrees.erase m0).attach,
      sgn (pcoef i m.1) * Real.sqrt |pcoef i m.1| *
        y ⟨⟨gradeVar m.1, gradeVar_mem_usedVars (Finset.mem_of_mem_erase m.2)⟩, by
          intro heq
          have hgv : gradeVar m.1 = gradeVar m0 := congrArg Subtype.val heq
          have hm1 : 1 ≤ m.1 := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase m.2)).1
          exact (Finset.mem_erase.mp m.2).1 (gradeVar_injOn hm1 hm0_pos hgv)⟩) +
    Real.sqrt (1 - ∑ m ∈ tableDegrees, |pcoef i m|) *
      y ⟨⟨g1 3, g1_mem_usedVars 3 (by decide)⟩, by
        intro heq
        exact (gradeVar_ne_g1 m0 3 (by decide)) (congrArg Subtype.val heq).symm⟩ +
    g y
  have hrest_meas : Measurable rest := by
    dsimp only [rest]
    refine Measurable.add (Measurable.add ?_ ?_) hg_meas
    · exact Finset.measurable_sum _ fun _ _ => measurable_const.mul (measurable_pi_apply _)
    · exact measurable_const.mul (measurable_pi_apply _)
  have hsplit : ∀ x : GPoint,
      Wfun' i x + extra x =
        (sgn (pcoef i m0) * Real.sqrt |pcoef i m0|) * x v0 + rest (fun w => x w.1.1) := by
    intro x
    unfold Wfun'
    rw [← Finset.add_sum_erase _ _ hm0, hg_eq x]
    have hsum : ∑ m ∈ tableDegrees.erase m0,
          sgn (pcoef i m) * Real.sqrt |pcoef i m| * x (gradeVar m) =
        ∑ m ∈ (tableDegrees.erase m0).attach,
          sgn (pcoef i m.1) * Real.sqrt |pcoef i m.1| * x (gradeVar m.1) :=
      (Finset.sum_attach (tableDegrees.erase m0) fun m =>
        sgn (pcoef i m) * Real.sqrt |pcoef i m| * x (gradeVar m)).symm
    dsimp only [rest]
    rw [hsum]
    ring
  simpa only [hsplit] using ae_linear_add_ne_zero usedVars v0 hv0 _ hcne rest hrest_meas

private lemma isGradedOdd_roundF (i : ℕ) (hi : i < 32) : IsGradedOdd (roundF i) := by
  unfold IsGradedOdd roundF
  by_cases hi14 : i = 14
  · subst hi14
    simp only [↓reduceIte]
    filter_upwards [ae_coord_ne_zero (gradeVar 5)] with x hx5
    rw [gradedFlip_gradeVar (by norm_num) (by decide),
      gradedFlip_gradeVar (by norm_num) (by decide)]
    exact Fstar_neg_neg hx5
  · by_cases hi17 : 17 ≤ i
    · simp only [hi14, ↓reduceIte, hi17]
      have hne := ae_Wfun_add_ne_zero i hi hi14 (fun _ => 0) ⟨fun _ => 0, measurable_const, fun _ => rfl⟩
      filter_upwards [hne] with x hx
      rw [add_zero] at hx
      rw [Wfun_gradedFlip, sgn_neg_of_ne_zero hx]
    · simp only [hi14, ↓reduceIte, hi17]
      have hne := ae_Wfun_add_ne_zero i hi hi14
        (fun x => rfun (x (g1 4)) + rfun (x (g1 5)) + rfun (x (g1 6)))
        ⟨fun y =>
          rfun (y ⟨⟨g1 4, g1_mem_usedVars 4 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 4 (by decide) (congrArg Subtype.val h).symm⟩) +
          rfun (y ⟨⟨g1 5, g1_mem_usedVars 5 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 5 (by decide) (congrArg Subtype.val h).symm⟩) +
          rfun (y ⟨⟨g1 6, g1_mem_usedVars 6 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 6 (by decide) (congrArg Subtype.val h).symm⟩),
          ((measurable_rfun.comp (measurable_pi_apply _)).add
            (measurable_rfun.comp (measurable_pi_apply _))).add
            (measurable_rfun.comp (measurable_pi_apply _)),
          fun _ => rfl⟩
      filter_upwards [hne] with x hx
      unfold Fgraph
      rw [Wfun_gradedFlip, gradedFlip_g1, gradedFlip_g1, gradedFlip_g1,
        rfun_neg, rfun_neg, rfun_neg]
      have hneg : -Wfun i x + (-rfun (x (g1 4)) + -rfun (x (g1 5)) + -rfun (x (g1 6))) =
          -(Wfun i x + (rfun (x (g1 4)) + rfun (x (g1 5)) + rfun (x (g1 6)))) := by ring
      rw [hneg, sgn_neg_of_ne_zero hx]

private lemma isGradedOdd_roundG (i : ℕ) (hi : i < 32) : IsGradedOdd (roundG i) := by
  unfold IsGradedOdd roundG
  by_cases hi14 : i = 14
  · subst hi14
    simp only [↓reduceIte]
    filter_upwards [ae_coord_ne_zero (gradeVar 5)] with x hx5
    rw [gradedFlip_gradeVar (by norm_num) (by decide),
      gradedFlip_gradeVar (by norm_num) (by decide)]
    exact Fstar_neg_neg hx5
  · by_cases hi17 : 17 ≤ i
    · simp only [hi14, ↓reduceIte, hi17]
      have hne := ae_Wfun'_add_ne_zero i hi hi14 (fun _ => 0) ⟨fun _ => 0, measurable_const, fun _ => rfl⟩
      filter_upwards [hne] with x hx
      rw [add_zero] at hx
      rw [Wfun'_gradedFlip, sgn_neg_of_ne_zero hx]
    · simp only [hi14, ↓reduceIte, hi17]
      have hne := ae_Wfun'_add_ne_zero i hi hi14
        (fun x => rfun (-x (g1 4)) + rfun (-x (g1 5)) + rfun (-x (g1 6)))
        ⟨fun y =>
          rfun (-y ⟨⟨g1 4, g1_mem_usedVars 4 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 4 (by decide) (congrArg Subtype.val h).symm⟩) +
          rfun (-y ⟨⟨g1 5, g1_mem_usedVars 5 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 5 (by decide) (congrArg Subtype.val h).symm⟩) +
          rfun (-y ⟨⟨g1 6, g1_mem_usedVars 6 (by decide)⟩, fun h =>
            gradeVar_ne_g1 _ 6 (by decide) (congrArg Subtype.val h).symm⟩),
          ((measurable_rfun.comp (measurable_pi_apply _).neg).add
            (measurable_rfun.comp (measurable_pi_apply _).neg)).add
            (measurable_rfun.comp (measurable_pi_apply _).neg),
          fun _ => rfl⟩
      filter_upwards [hne] with x hx
      unfold Fgraph
      rw [Wfun'_gradedFlip, gradedFlip_g1, gradedFlip_g1, gradedFlip_g1,
        neg_neg, neg_neg, neg_neg]
      have hneg : -Wfun' i x + (rfun (x (g1 4)) + rfun (x (g1 5)) + rfun (x (g1 6))) =
          -(Wfun' i x + (rfun (-x (g1 4)) + rfun (-x (g1 5)) + rfun (-x (g1 6)))) := by
        rw [rfun_neg, rfun_neg, rfun_neg]; ring
      rw [hneg, sgn_neg_of_ne_zero hx]

/-! ### 5. The mixture `cMix` belongs to `KSet` -/

private noncomputable def mixMeasure : Measure (Fin 32) :=
  ∑ i : Fin 32, ENNReal.ofReal (lam i.1) • Measure.dirac i

private lemma isProbabilityMeasure_mixMeasure : IsProbabilityMeasure mixMeasure := by
  constructor
  unfold mixMeasure
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => lam_nonneg i.1), Fin.sum_univ_eq_sum_range,
    sum_lam, ENNReal.ofReal_one]

private noncomputable def mixScheme : GradedScheme where
  Ω := Fin 32
  μ := mixMeasure
  prob := isProbabilityMeasure_mixMeasure
  F := fun i x => roundF i.1 x
  G := fun i x => roundG i.1 x
  measurable_F := measurable_from_prod_countable_right fun i => measurable_roundF i.1
  measurable_G := measurable_from_prod_countable_right fun i => measurable_roundG i.1
  bool_F := fun i => isAsympBoolean_roundF i.1
  bool_G := fun i => isAsympBoolean_roundG i.1
  odd_F := fun i => isGradedOdd_roundF i.1 i.2
  odd_G := fun i => isGradedOdd_roundG i.1 i.2

private lemma mixScheme_coeffSeq (m : ℕ) : mixScheme.coeffSeq m = cMix m := by
  unfold GradedScheme.coeffSeq mixScheme cMix Hcoef
  dsimp only
  have : IsProbabilityMeasure mixMeasure := isProbabilityMeasure_mixMeasure
  rw [integral_fintype Integrable.of_finite]
  rw [← Fin.sum_univ_eq_sum_range (fun i => lam i * gradedInner m (roundF i) (roundG i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 1
  rw [Measure.real_def]
  unfold mixMeasure
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (MeasurableSet.singleton i), Set.indicator_singleton,
    Pi.one_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact ENNReal.toReal_ofReal (lam_nonneg i.1)

private lemma cMix_mem_KSet : cMix ∈ KSet :=
  ⟨mixScheme, funext fun m => (mixScheme_coeffSeq m).symm⟩

/-! ### 6. Continuity of `krivineValue` on `ℓ¹` and upper bound on `K_G` -/

private lemma lp_one_summable (a : lp (fun _ : ℕ => ℝ) 1) : Summable fun m => |a m| := by
  have h := (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)
  simpa [Real.norm_eq_abs] using h

private lemma lp_one_norm_eq_tsum (a : lp (fun _ : ℕ => ℝ) 1) : ‖a‖ = ∑' m, |a m| := by
  rw [lp.norm_eq_tsum_rpow (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)]
  simp [Real.norm_eq_abs]

private lemma abs_krivineValue_sub_le (a b : lp (fun _ : ℕ => ℝ) 1) :
    |krivineValue (⇑a) - krivineValue (⇑b)| ≤ 2 * ‖a - b‖ := by
  unfold krivineValue
  have ha_odd : Summable fun k => |a (2 * k + 3)| :=
    (lp_one_summable a).comp_injective (fun _ _ h => by omega)
  have hb_odd : Summable fun k => |b (2 * k + 3)| :=
    (lp_one_summable b).comp_injective (fun _ _ h => by omega)
  have hab : Summable fun m => |a m - b m| := by
    simpa [lp.coeFn_sub, Pi.sub_apply] using lp_one_summable (a - b)
  have hab_odd : Summable fun k => |a (2 * k + 3) - b (2 * k + 3)| :=
    hab.comp_injective (fun _ _ h => by omega)
  have h1 : |a 1 - b 1| ≤ ‖a - b‖ := by
    simpa [lp.coeFn_sub, Pi.sub_apply, Real.norm_eq_abs] using
      lp.norm_apply_le_norm (p := (1 : ENNReal)) one_ne_zero (a - b) 1
  have h2 : |(∑' k, |a (2 * k + 3)|) - (∑' k, |b (2 * k + 3)|)| ≤ ‖a - b‖ := by
    rw [← ha_odd.tsum_sub hb_odd]
    have hdiff_summ : Summable fun k => ‖|a (2 * k + 3)| - |b (2 * k + 3)|‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun k => by
          rw [Real.norm_eq_abs]
          exact abs_abs_sub_abs_le_abs_sub (a (2 * k + 3)) (b (2 * k + 3)))
        hab_odd
    calc |∑' k, (|a (2 * k + 3)| - |b (2 * k + 3)|)|
        ≤ ∑' k, |(|a (2 * k + 3)| - |b (2 * k + 3)|)| := by
          simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff_summ
      _ ≤ ∑' k, |a (2 * k + 3) - b (2 * k + 3)| :=
          Summable.tsum_le_tsum (fun k => abs_abs_sub_abs_le_abs_sub _ _)
            (by simpa only [Real.norm_eq_abs] using hdiff_summ) hab_odd
      _ ≤ ∑' m, |a m - b m| :=
          tsum_comp_le_tsum_of_inj hab (fun _ => abs_nonneg _) (fun _ _ h => by omega)
      _ = ‖a - b‖ := by
          rw [lp_one_norm_eq_tsum (a - b)]
          simp
  have hrew : (a 1 - ∑' k, |a (2 * k + 3)|) - (b 1 - ∑' k, |b (2 * k + 3)|) =
      (a 1 - b 1) - ((∑' k, |a (2 * k + 3)|) - (∑' k, |b (2 * k + 3)|)) := by ring
  rw [hrew]
  calc |(a 1 - b 1) - ((∑' k, |a (2 * k + 3)|) - (∑' k, |b (2 * k + 3)|))|
      ≤ |a 1 - b 1| + |(∑' k, |a (2 * k + 3)|) - (∑' k, |b (2 * k + 3)|)| := abs_sub _ _
    _ ≤ ‖a - b‖ + ‖a - b‖ := add_le_add h1 h2
    _ = 2 * ‖a - b‖ := by ring

private lemma continuous_krivineValue_lp :
    Continuous (fun c : lp (fun _ : ℕ => ℝ) 1 => krivineValue (⇑c)) := by
  refine (LipschitzWith.of_dist_le_mul (K := 2) fun a b => ?_).continuous
  simpa [Real.dist_eq, dist_eq_norm] using abs_krivineValue_sub_le a b

private lemma krivineValue_cMix_le_inv_grothendieckConst :
    krivineValue cMix ≤ (GrothendieckConstant.grothendieckConst)⁻¹ := by
  have hmem_lp : Memℓp cMix 1 := lemma_3_3.1 cMix cMix_mem_KSet
  let cMix_lp : lp (fun _ : ℕ => ℝ) 1 := ⟨cMix, hmem_lp⟩
  have hclos : cMix_lp ∈ closure {c : lp (fun _ : ℕ => ℝ) 1 | ⇑c ∈ CSet} := by
    rw [← lemma_3_3.2]
    exact cMix_mem_KSet
  have hclosed : IsClosed {c : lp (fun _ : ℕ => ℝ) 1 |
      krivineValue (⇑c) ≤ (GrothendieckConstant.grothendieckConst)⁻¹} :=
    isClosed_le continuous_krivineValue_lp continuous_const
  have hsub : {c : lp (fun _ : ℕ => ℝ) 1 | ⇑c ∈ CSet} ⊆
      {c : lp (fun _ : ℕ => ℝ) 1 |
        krivineValue (⇑c) ≤ (GrothendieckConstant.grothendieckConst)⁻¹} := by
    rintro c ⟨n, S, hS, hc⟩
    change krivineValue (⇑c) ≤ _
    rw [hc]
    exact lemma_2_1 n S hS
  exact closure_minimal hsub hclosed hclos

end GrothendieckPDTheorem42Aux

open GrothendieckPDTheorem42Aux

theorem solution :
    (Summable fun k => |cMix (2 * k + 3)|) ∧
      (0.561831528950464991 : ℝ) < cMix 1 - ∑' k, |cMix (2 * k + 3)| ∧
      (1000000 / 1779893 : ℝ) < 0.561831528950464991 ∧
      GrothendieckConstant.grothendieckConst < 1779893 / 1000000 := by
  have h1 : Summable fun k => |cMix (2 * k + 3)| := summable_abs_cMix_odd
  have h2 : (0.561831528950464991 : ℝ) < cMix 1 - ∑' k, |cMix (2 * k + 3)| := krivineValue_cMix_gt
  have h3 : (1000000 / 1779893 : ℝ) < 0.561831528950464991 := by norm_num
  have h4 : GrothendieckConstant.grothendieckConst < 1779893 / 1000000 := by
    have hle : krivineValue cMix ≤ (GrothendieckConstant.grothendieckConst)⁻¹ :=
      krivineValue_cMix_le_inv_grothendieckConst
    have hlt : (1000000 / 1779893 : ℝ) < (GrothendieckConstant.grothendieckConst)⁻¹ := by
      unfold krivineValue at hle
      linarith
    have hinv_pos : 0 < (GrothendieckConstant.grothendieckConst)⁻¹ :=
      lt_trans (by norm_num) hlt
    have hK_pos : 0 < GrothendieckConstant.grothendieckConst := inv_pos.mp hinv_pos
    have hmul : (1000000 / 1779893 : ℝ) * GrothendieckConstant.grothendieckConst < 1 := by
      calc (1000000 / 1779893 : ℝ) * GrothendieckConstant.grothendieckConst
          < (GrothendieckConstant.grothendieckConst)⁻¹ *
              GrothendieckConstant.grothendieckConst :=
            mul_lt_mul_of_pos_right hlt hK_pos
        _ = 1 := inv_mul_cancel₀ hK_pos.ne'
    linarith
  exact ⟨h1, h2, h3, h4⟩

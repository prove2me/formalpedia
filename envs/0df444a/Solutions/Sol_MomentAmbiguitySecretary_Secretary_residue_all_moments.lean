-- Prove2me | solution 1 for MomentAmbiguitySecretary.Secretary.residue_all_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:56.648413+00:00
-- url     : https://prove2.me/submissions/b8397373-78ce-4056-a764-ec53f666aa9a

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Separator
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_entire_product_coefficients
import Theorems.Thm_MomentAmbiguitySecretary_Secretary_residue_moment_sums

section
open MeasureTheory Set Filter
open scoped BigOperators Topology NNReal ENNReal

namespace MomentAmbiguitySecretary.Secretary.Dev.ResidueMoments

open MomentAmbiguitySecretary.Secretary

lemma coef_nonneg (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (j : ℕ) : 0 ≤ coefficient B N j := by
  refine ge_of_tendsto' ((entire_product_coefficients B N hB hN).2.2.2.2.2 j).2.1 fun M => ?_
  unfold finiteOccupancySum
  refine Finset.sum_nonneg fun c _ => ?_
  split_ifs
  · positivity
  · exact le_rfl

lemma moment (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N) (h : Fin N) (t : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (residueMeasure B N h.val) ∧
    (∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h.val) = residueSum B N h.val t / normalizer B N := by
  obtain ⟨hA, -, hW1, -⟩ := residue_moment_sums B N hB hN
  have hW : 0 < normalizer B N := by linarith
  have hsum := (hA t h).1.summable
  have hc : ∀ j : ℕ, (ENNReal.ofReal (if j % N = h.val then coefficient B N j / normalizer B N
      else 0)).toReal = if j % N = h.val then coefficient B N j / normalizer B N else 0 := by
    intro j
    rw [ENNReal.toReal_ofReal]
    split_ifs
    · have := coef_nonneg B N hB hN j
      positivity
    · exact le_rfl
  have hterm : ∀ j : ℕ, (if j % N = h.val then coefficient B N j / normalizer B N else 0) *
      ((((B : ℝ≥0) ^ j : ℝ≥0) : ℝ) ^ t) = residueTerm B N h.val t j / normalizer B N := by
    intro j
    unfold residueTerm
    split_ifs
    · push_cast
      rw [← pow_mul, mul_comm j t]; ring
    · simp
  unfold residueMeasure
  constructor
  · refine integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top) ?_
    simp_rw [hc, Real.norm_eq_abs]
    refine (hsum.div_const (normalizer B N)).congr fun j => ?_
    rw [← hterm j, abs_of_nonneg (by positivity)]
  · rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
    simp_rw [hc, smul_eq_mul, hterm]
    rw [tsum_div_const]
    rfl

end MomentAmbiguitySecretary.Secretary.Dev.ResidueMoments

namespace MomentAmbiguitySecretary.Secretary

open MomentAmbiguitySecretary.Secretary.Dev.ResidueMoments

theorem chk_residue_all_moments (B N : ℕ) (hB : 2 ≤ B) (hN : 2 ≤ N)
    (h h' : Fin N) (t : ℕ) :
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (residueMeasure B N h.val) ∧
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ t) (residueMeasure B N h'.val) ∧
    (∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h.val) =
      ∫ x : ℝ≥0, (x : ℝ) ^ t ∂residueMeasure B N h'.val := by
  obtain ⟨hA, -, -, -⟩ := residue_moment_sums B N hB hN
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  obtain ⟨i1, e1⟩ := moment B N hB hN h t
  obtain ⟨i2, e2⟩ := moment B N hB hN h' t
  refine ⟨i1, i2, ?_⟩
  rw [e1, e2]
  congr 1
  have a1 := (hA t h).2
  have a2 := (hA t h').2
  rw [← a2] at a1
  exact_mod_cast a1

end MomentAmbiguitySecretary.Secretary

end

theorem solution : type_of% @MomentAmbiguitySecretary.Secretary.chk_residue_all_moments := @MomentAmbiguitySecretary.Secretary.chk_residue_all_moments

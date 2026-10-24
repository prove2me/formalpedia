-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_real_power_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:31:51.621031+00:00
-- url     : https://prove2.me/submissions/cf1f1b22-14e9-45ad-b672-0c698c661114

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

section

open MeasureTheory Set

namespace PiSimplex

noncomputable section

/-- the simplex `{x ≥ 0, ∑ x ≤ c}` -/
def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

lemma S_closed (n : ℕ) (c : ℝ) : IsClosed (S n c) := by
  unfold S
  refine IsClosed.inter ?_ ?_
  · have := isClosed_iInter fun i : Fin n =>
      isClosed_le (continuous_const (y := (0 : ℝ))) (continuous_apply (A := fun _ : Fin n => ℝ) i)
    rw [Set.iInter_setOf] at this
    exact this
  · exact isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const

lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := (S_closed n c).measurableSet

lemma S_neg (n : ℕ) {c : ℝ} (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  intro h
  exact lt_of_lt_of_le hc (Finset.sum_nonneg fun i _ => h i)

lemma slice (n : ℕ) (c t : ℝ) :
    {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} =
      if 0 ≤ t then S n (c - t) else ∅ := by
  ext y
  simp only [S, mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  split_ifs with h
  · simp only [h, true_and, mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · simp [h]

/-- the value of the volume -/
def F (n : ℕ) (c : ℝ) : ENNReal := if 0 ≤ c then ENNReal.ofReal (c ^ n / n.factorial) else 0

lemma integral_pow_sub (n : ℕ) (c : ℝ) :
    ∫ t in (0 : ℝ)..c, (c - t) ^ n / n.factorial = c ^ (n + 1) / (n + 1).factorial := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]
  simp only [sub_self, sub_zero, integral_pow]
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma vol_succ (n : ℕ) (c : ℝ) :
    volume (S (n + 1) c) = ∫⁻ t, (if 0 ≤ t then volume (S n (c - t)) else 0) := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  rw [← h.measure_preimage_equiv (S (n + 1) c)]
  rw [show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi (fun _ => volume) from rfl] at h
  rw [Measure.volume_eq_prod, Measure.prod_apply]
  · congr 1
    ext t
    have : Prod.mk t ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ⁻¹'
        S (n + 1) c) = {y : Fin n → ℝ | (Fin.cons t y : Fin (n + 1) → ℝ) ∈ S (n + 1) c} := by
      ext y
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    rw [this, slice]
    split_ifs <;> simp
  · exact (MeasurableEquiv.measurable _) (S_meas _ _)

theorem vol_S (n : ℕ) (c : ℝ) : volume (S n c) = F n c := by
  induction n generalizing c with
  | zero =>
    unfold F
    split_ifs with hc
    · have : S 0 c = univ := by
        ext x; simp [S, hc]
      rw [this, volume_pi, Measure.pi_univ]; simp
    · rw [S_neg 0 (lt_of_not_ge hc)]; simp
  | succ n ih =>
    rw [vol_succ]
    simp_rw [ih]
    unfold F
    split_ifs with hc
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = (Icc 0 c).indicator (fun t => ENNReal.ofReal ((c - t) ^ n / n.factorial)) := by
        ext t
        simp only [indicator, mem_Icc, sub_nonneg]
        split_ifs <;> first | rfl | (exfalso; tauto)
      rw [this, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc, integral_pow_sub]
      · exact (Continuous.integrableOn_Icc (by fun_prop))
      · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun t ht => ?_)
        have : 0 ≤ c - t := by linarith [ht.2]
        positivity
    · have : (fun t : ℝ => if 0 ≤ t then (if 0 ≤ c - t then ENNReal.ofReal ((c - t) ^ n / n.factorial)
          else 0) else 0) = fun _ => 0 := by
        ext t
        split_ifs with h1 h2 <;> first | rfl | (exfalso; linarith)
      rw [this]; simp

theorem vol_S_of_nonneg (n : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n / n.factorial) := by
  rw [vol_S, F, if_pos hc]

end

end PiSimplex

end

section

open MeasureTheory Set PiSimplex
namespace PiL

lemma S_eq (n : ℕ) (c : ℝ) : {x : Fin n → ℝ | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c} = S n c := rfl

lemma int01 (n : ℕ) : ∫ t in (0:ℝ)..1, (1 - t) ^ n = 1 / (n + 1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => t ^ n)]; simp [integral_pow]

lemma fact_ofReal (n : ℕ) : ENNReal.ofReal (1 / (n+1).factorial) =
    ENNReal.ofReal (1 / n.factorial) * ENNReal.ofReal (1 / (n + 1)) := by
  rw [← ENNReal.ofReal_mul (by positivity), Nat.factorial_succ]; push_cast; congr 1; field_simp

theorem A (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
          (Finset.univ.sum fun i : Fin n => x i) ≤ 1} *
        ENNReal.ofReal (∫ t in (0 : Real)..1, (1 - t) ^ n) := by
  rw [S_eq, S_eq, vol_S_of_nonneg _ zero_le_one, vol_S_of_nonneg _ zero_le_one, int01]
  simpa using fact_ofReal n

theorem B (n : Nat) :
    MeasureTheory.volume
        {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} =
      MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} *
        ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) := by
  rw [S_eq, S_eq, vol_S_of_nonneg _ zero_le_one, vol_S_of_nonneg _ zero_le_one]
  simpa using fact_ofReal n

theorem C (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ r} =
      ENNReal.ofReal (r ^ n) * MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1} := by
  rw [S_eq, S_eq, vol_S_of_nonneg _ hr, vol_S_of_nonneg _ zero_le_one, ← ENNReal.ofReal_mul (by positivity), one_pow]
  congr 1; field_simp

theorem E (A : Real) (hA : 0 ≤ A) :
    (MeasureTheory.volume {x : Fin 0 → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin 0, x i ≤ A}).toReal = 1 := by
  rw [S_eq, vol_S_of_nonneg _ hA]; simp

theorem F (m : Nat) (A : Real) (hA : 0 ≤ A) :
    ∫ t in Set.Icc (0 : Real) A, (A - t) ^ m / ((Nat.factorial m : Nat) : Real) =
      A ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hA, integral_pow_sub]

theorem G (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)) (fun t : Real => (T - t) ^ n / (n.factorial : Real)) = T ^ (n + 1) / ((n + 1).factorial : Real) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le, integral_pow_sub]

lemma toReal_S (m : ℕ) {T : ℝ} (hT : 0 ≤ T) : (volume (S m T)).toReal = T ^ m / m.factorial := by
  rw [vol_S_of_nonneg _ hT, ENNReal.toReal_ofReal (by positivity)]

theorem H (m : Nat) (H : Real) (hH : 0 < H)
    (ih : ∀ (T : Real), 0 < T →
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ T}).toReal =
        T ^ m / ((Nat.factorial m : Nat) : Real)) :
    (∫ t in (0 : Real)..H,
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal) =
      H ^ (m + 1) / ((Nat.factorial (m + 1) : Nat) : Real) := by
  rw [← integral_pow_sub]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hH.le] at ht
  rw [S_eq, toReal_S _ (by linarith [ht.2])]

lemma slice_vol (m : ℕ) (H t : ℝ) : (volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal
    = (Icc 0 H).indicator (fun t => (H - t) ^ m / m.factorial) t := by
  by_cases ht : 0 ≤ t
  · simp only [ht, true_and]
    rw [S_eq]
    by_cases h2 : t ≤ H
    · rw [toReal_S _ (by linarith), indicator_of_mem (show t ∈ Icc 0 H from ⟨ht, h2⟩)]
    · rw [S_neg _ (by linarith), indicator_of_notMem (show t ∉ Icc 0 H from fun h => h2 h.2)]; simp
  · rw [indicator_of_notMem (show t ∉ Icc 0 H from fun h => ht h.1)]; simp [ht]

theorem J (m : Nat) (H : Real) (hH : 0 < H) :
    (∫ t : Real,
        (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal) =
      ∫ t in (0 : Real)..H,
        (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by
  simp_rw [slice_vol]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hH.le]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hH.le] at ht
  rw [S_eq, toReal_S _ (by linarith [ht.2])]

theorem I (m : Nat) (H : Real) :
    (MeasureTheory.volume {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H}).toReal =
      ∫ t : Real,
        (MeasureTheory.volume {x : Fin m → Real | 0 ≤ t ∧ (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ H - t}).toReal := by
  simp_rw [slice_vol]
  rw [integral_indicator measurableSet_Icc, S_eq]
  by_cases hH : 0 ≤ H
  · rw [toReal_S _ hH, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hH, integral_pow_sub]
  · rw [S_neg _ (by linarith), Icc_eq_empty (by linarith)]; simp

theorem K (n : Nat) :
    (MeasureTheory.volume {x : Fin (n + 1) → Real | (∀ i : Fin (n + 1), 0 ≤ x i) ∧
      ∑ i : Fin (n + 1), x i ≤ 1}).toReal =
      ∫ t in (0 : Real)..1, (MeasureTheory.volume {y : Fin n → Real |
        (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1 - t}).toReal := by
  rw [I, J _ _ one_pos]

theorem L (m : Nat) (A : Real) :
    (∫ t in Set.Icc (0 : Real) A,
      (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈
        {x : Fin (m + 1) → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin (m + 1), x i ≤ A}}).toReal) =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧
          ∑ i : Fin m, y i ≤ A - t}).toReal := by
  refine setIntegral_congr_fun measurableSet_Icc fun t ht => ?_
  rw [S_eq (m + 1), slice, if_pos ht.1]; rfl
end PiL

end

open scoped BigOperators

theorem solution (n : Nat) (T : Real) (hT : 0 < T) : MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : Real) T)) (fun t : Real => (T - t) ^ n / (n.factorial : Real)) = T ^ (n + 1) / ((n + 1).factorial : Real) := by
  apply PiL.G <;> assumption

-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_eq_unweighted_div_weights
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:36:50.055385+00:00
-- url     : https://prove2.me/submissions/4e7d718c-d5c3-484b-a5b8-536a4114d274

import Mathlib
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

namespace PiL2

lemma diag_apply {m : ℕ} (w : Fin m → ℝ) (x : Fin m → ℝ) :
    (Matrix.diagonal w).toLin' x = fun i => w i * x i := by
  ext i; simp [Matrix.mulVec_diagonal]

lemma vol_diag {m : ℕ} (w : Fin m → ℝ) (s : Set (Fin m → ℝ)) :
    volume ((fun x : Fin m → ℝ => fun i => w i * x i) '' s) =
      ENNReal.ofReal |∏ i, w i| * volume s := by
  have := Measure.addHaar_image_linearMap (volume : Measure (Fin m → ℝ)) (Matrix.diagonal w).toLin' s
  have hf : ⇑(Matrix.diagonal w).toLin' = fun x i => w i * x i := funext (diag_apply w)
  rw [LinearMap.det_toLin', Matrix.det_diagonal, hf] at this
  exact this

theorem diag_toReal {m : Nat} (w : Fin m → Real) (hw : ∀ i, w i ≠ 0) (s : Set (Fin m → Real)) (hs : MeasurableSet s) :
    (MeasureTheory.volume ((fun x : Fin m → Real => fun i => w i * x i) '' s)).toReal =
      |(∏ i : Fin m, w i)| * (MeasureTheory.volume s).toReal := by
  rw [vol_diag, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]

lemma weighted_image {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) :
    (fun x : Fin m → ℝ => fun i => w i * x i) '' {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H} = S m H := by
  ext y
  simp only [mem_image, mem_setOf_eq, S]
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨fun i => mul_nonneg (hw i).le (h1 i), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => y i / w i, ⟨fun i => div_nonneg (h1 i) (hw i).le, ?_⟩, ?_⟩
    · convert h2 using 2 with i; field_simp [(hw i).ne']
    · ext i; field_simp [(hw i).ne']

theorem weighted_div {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have := vol_diag w {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}
  rw [weighted_image w hw] at this
  change _ = (volume (S m H)).toReal / _
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos hp]
  field_simp

theorem weighted_formula {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i}).toReal =
      (B + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  rw [weighted_div w _ hw (by linarith)]
  change (volume (S m _)).toReal / _ = _
  rw [vol_S_of_nonneg _ (by linarith), ENNReal.toReal_ofReal (by positivity)]

end PiL2

end

open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ H}).toReal =
      (MeasureTheory.volume {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ H}).toReal / ∏ i : Fin m, w i := by
  apply PiL2.weighted_div <;> assumption

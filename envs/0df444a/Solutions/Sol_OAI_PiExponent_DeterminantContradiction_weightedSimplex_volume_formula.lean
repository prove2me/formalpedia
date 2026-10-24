-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_volume_formula
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:20:35.333128+00:00
-- url     : https://prove2.me/submissions/24fa887e-a7b3-459a-a335-a4051c6b7a96

import Mathlib
import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open MeasureTheory
open scoped BigOperators Pointwise

namespace PXSc

def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (Finset.univ.sum fun i : Fin n => x i) ≤ c}

lemma image_eq (n : ℕ) (a : ℝ) :
    (fun y : Fin n → ℝ => fun i => a * y i) '' S n 1 = a • S n 1 := by
  rw [← Set.image_smul]; rfl

lemma S_eq_smul (n : ℕ) (c : ℝ) (hc : 0 ≤ c) : S n c = c • S n 1 := by
  ext x
  constructor
  · rintro ⟨h0, hs⟩
    rcases hc.eq_or_lt with rfl | hc'
    · refine ⟨0, ⟨fun i => le_rfl, by simp⟩, ?_⟩
      have hx : ∀ i, x i = 0 := by
        intro i
        have hle : x i ≤ ∑ j, x j :=
          Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
        exact le_antisymm (hle.trans hs) (h0 i)
      funext i; simp [hx i]
    · refine ⟨c⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc) (h0 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hc']; simpa using hs
      · simp [smul_smul, hc'.ne']
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      simpa using mul_le_mul_of_nonneg_left hs hc

lemma vol_smul (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S n 1) = ENNReal.ofReal (a ^ n) * volume (S n 1) := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg ha n)]


lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := by
  unfold S
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const

lemma S_neg (n : ℕ) (c : ℝ) (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h0
  exact lt_of_lt_of_le hc (Finset.sum_nonneg (fun i _ => h0 i))

lemma vol_S (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n) * volume (S n 1) := by
  rw [S_eq_smul n c hc]; exact vol_smul n c hc

end PXSc

namespace PXSl

lemma slice (m : ℕ) (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    volume s = ∫⁻ t, volume {y : Fin m → ℝ | Fin.cons t y ∈ s} := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hs' : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurable hs
  rw [← hp.measure_preimage hs.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hs']
  refine lintegral_congr (fun t => ?_)
  congr 1
  ext y
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

end PXSl

namespace PXSV
open PXSc

lemma slice_S (n : ℕ) (t : ℝ) :
    {y : Fin n → ℝ | Fin.cons t y ∈ S (n + 1) 1} =
      (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅) := by
  ext y
  simp only [S, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · rw [if_pos ht]
    simp only [S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨ht.1, h1⟩, by linarith⟩
  · rw [if_neg ht]
    simp only [Set.mem_empty_iff_false, iff_false, not_and, not_le]
    rintro ⟨h0, h1⟩
    have hs : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => h1 i)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact absurd h0 (not_le.2 ht)
    · linarith

lemma integral_pow (n : ℕ) :
    ∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ n)]
    simp [integral_pow]
  · exact (continuous_const.sub continuous_id |>.pow n).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (by linarith [ht.2]) n

theorem succ (n : ℕ) :
    volume (S (n + 1) 1) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) * volume (S n 1) := by
  rw [PXSl.slice n _ (S_meas _ _)]
  simp_rw [slice_S]
  have : ∀ t, volume (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅)
      = Set.indicator (Set.Icc (0:ℝ) 1) (fun t => ENNReal.ofReal ((1 - t) ^ n) * volume (S n 1)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0:ℝ) 1
    · rw [if_pos ht, Set.indicator_of_mem ht, vol_S n _ (by linarith [ht.2])]
    · rw [if_neg ht, Set.indicator_of_notMem ht]; simp
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const _ (by fun_prop), integral_pow]

end PXSV

namespace PXSV
open PXSc

theorem vol_one (n : ℕ) : volume (S n 1) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  induction n with
  | zero =>
    have : S 0 1 = Set.univ := by
      ext x; simp [S]
    rw [this, volume_pi, Measure.pi_of_empty (x := fun i => (Fin.elim0 i : ℝ))]
    simp
  | succ n ih =>
    rw [succ, ih, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    field_simp

end PXSV

namespace PXDg

lemma image_vol {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (s : Set (Fin m → ℝ)) :
    volume ((fun y : Fin m → ℝ => fun i => y i / w i) '' s)
      = ENNReal.ofReal (∏ i, (w i)⁻¹) * volume s := by
  have hf : (fun y : Fin m → ℝ => fun i => y i / w i)
      = ⇑(Matrix.toLin' (Matrix.diagonal fun i => (w i)⁻¹)) := by
    funext y i
    rw [Matrix.toLin'_apply, Matrix.mulVec_diagonal, div_eq_inv_mul]
  rw [hf, Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_diagonal,
    abs_of_pos (Finset.prod_pos (fun i _ => inv_pos.2 (hw i)))]

lemma weighted_eq {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (B : ℝ) :
    {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B}
      = (fun y : Fin m → ℝ => fun i => y i / w i) '' PXSc.S m B := by
  ext x
  constructor
  · rintro ⟨h0, hs⟩
    refine ⟨fun i => w i * x i, ⟨fun i => mul_nonneg (hw i).le (h0 i), hs⟩, ?_⟩
    funext i; field_simp [(hw i).ne']
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => div_nonneg (h0 i) (hw i).le, ?_⟩
    have : ∀ i, w i * (y i / w i) = y i := fun i => by field_simp [(hw i).ne']
    simp only [this]; exact hs

end PXDg

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction in
theorem solution {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B}).toReal =
      B ^ m / ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  rw [PXDg.weighted_eq w hw B, PXDg.image_vol w hw, PXSc.vol_S m B hB.le, PXSV.vol_one]
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  simp only [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg (fun i _ => (inv_pos.2 (hw i)).le)),
    ENNReal.toReal_ofReal (pow_nonneg hB.le m), ENNReal.toReal_ofReal (by positivity),
    Finset.prod_inv_distrib]
  field_simp

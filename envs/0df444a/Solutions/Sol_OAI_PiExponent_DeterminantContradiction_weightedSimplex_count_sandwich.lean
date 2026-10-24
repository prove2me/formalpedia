-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_count_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:24:04.798464+00:00
-- url     : https://prove2.me/submissions/e3863222-148e-450c-a095-244ae46e2320

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

open OAI.PiExponent
namespace PXUB

lemma box_eq {m : ℕ} (a : Fin m → ℕ) :
    {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}
      = Set.univ.pi (fun i => Set.Ico (a i : ℝ) ((a i : ℝ) + 1)) := by
  ext x; simp [Set.mem_pi]

lemma box_vol {m : ℕ} (a : Fin m → ℕ) :
    MeasureTheory.volume {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} = 1 := by
  rw [box_eq, Real.volume_pi_Ico]
  simp

lemma box_meas {m : ℕ} (a : Fin m → ℕ) :
    MeasurableSet {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1} := by
  rw [box_eq]; exact MeasurableSet.univ_pi (fun i => measurableSet_Ico)

lemma box_disj {m : ℕ} (s : Finset (Fin m → ℕ)) :
    (s : Set (Fin m → ℕ)).PairwiseDisjoint
      (fun a => {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) := by
  intro a _ b _ hab
  rw [Function.onFun, Set.disjoint_left]
  intro x hxa hxb
  apply hab
  funext i
  have h1 := hxa i; have h2 := hxb i

  have : (a i : ℝ) < b i + 1 := by linarith [h1.1, h2.2]
  have : (b i : ℝ) < a i + 1 := by linarith [h2.1, h1.2]
  have e1 : a i < b i + 1 := by exact_mod_cast ‹(a i : ℝ) < b i + 1›
  have e2 : b i < a i + 1 := by exact_mod_cast ‹(b i : ℝ) < a i + 1›
  omega

lemma union_vol {m : ℕ} (s : Finset (Fin m → ℕ)) :
    MeasureTheory.volume
      (⋃ a ∈ s, {x : Fin m → Real | ∀ i, (a i : Real) ≤ x i ∧ x i < (a i : Real) + 1}) = s.card := by
  rw [MeasureTheory.measure_biUnion_finset (box_disj s) (fun a _ => box_meas a)]
  simp [box_vol]

end PXUB


namespace PXCS
open OAI.PiExponent PXSc

def W {n : ℕ} (w : Fin n → ℝ) (B : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ B}

lemma wvol {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (B : ℝ) (hB : 0 < B) :
    volume (W w B) = ENNReal.ofReal (B ^ n / ((n.factorial : ℝ) * ∏ i, w i)) := by
  unfold W
  rw [PXDg.weighted_eq w hw B, PXDg.image_vol w hw, PXSc.vol_S n B hB.le, PXSV.vol_one,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (Finset.prod_nonneg (fun i _ => (inv_pos.2 (hw i)).le))]
  congr 1
  have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  rw [Finset.prod_inv_distrib]
  field_simp

lemma vol_le_card {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (T : ℝ) :
    volume {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      ≤ (strictWeightedSimplex w T).card := by
  classical
  rw [← PXUB.union_vol]
  apply MeasureTheory.measure_mono
  rintro x ⟨h0, hs⟩
  set a : Fin n → ℕ := fun i => ⌊x i⌋₊ with ha
  have hax : ∀ i, (a i : ℝ) ≤ x i := fun i => Nat.floor_le (h0 i)
  have hsa : ∑ i, w i * (a i : ℝ) ≤ ∑ i, w i * x i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i).le)
  have hmem : a ∈ strictWeightedSimplex w T := by
    unfold strictWeightedSimplex realWeightedSimplex
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨⟨fun i => ?_, by linarith⟩, by linarith⟩
    have hle : w i * x i ≤ ∑ j, w j * x j :=
      Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (h0 j))
        (Finset.mem_univ i)
    have hxi : x i ≤ T / w i := by
      rw [le_div_iff₀ (hw i)]; linarith
    have : a i ≤ ⌊T / w i⌋₊ := Nat.floor_le_floor hxi
    omega
  simp only [Set.mem_iUnion]
  exact ⟨a, hmem, fun i => ⟨hax i, Nat.lt_floor_add_one (x i)⟩⟩

lemma card_le_vol {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) :
    ((strictWeightedSimplex w H).card : ENNReal) ≤ volume (W w (H + ∑ i, w i)) := by
  classical
  rw [← PXUB.union_vol]
  apply MeasureTheory.measure_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨a, ha, hxa⟩ := hx
  have ha' : ∑ i, w i * (a i : ℝ) < H := by
    unfold strictWeightedSimplex at ha
    exact (Finset.mem_filter.1 ha).2
  refine ⟨fun i => le_trans (Nat.cast_nonneg _) (hxa i).1, ?_⟩
  have : ∑ i, w i * x i ≤ ∑ i, (w i * (a i : ℝ) + w i) :=
    Finset.sum_le_sum (fun i _ => by nlinarith [(hxa i).2, hw i])
  rw [Finset.sum_add_distrib] at this
  linarith

theorem sandwich (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ᶠ H : ℝ in Filter.atTop,
      ((H - ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) ≤
          ((strictWeightedSimplex w H).card : ℝ) ∧
        ((strictWeightedSimplex w H).card : ℝ) ≤
          ((H + ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) := by
  have hs0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => (hw i).le)
  filter_upwards [Filter.eventually_gt_atTop (∑ i, w i)] with H hH
  have hH0 : 0 < H := lt_of_le_of_lt hs0 hH
  constructor
  · have hsub : W w (H - ∑ i, w i) ⊆ {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < H} := by
      rintro x ⟨h0, hx⟩
      refine ⟨h0, ?_⟩
      by_cases hn : n = 0
      · subst hn; simpa using hH0
      · have : 0 < ∑ i, w i := by
          haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
          exact Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
        linarith
    have h1 := (measure_mono hsub).trans (vol_le_card w hw H)
    rw [wvol w hw _ (by linarith)] at h1
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) h1
    rwa [ENNReal.toReal_ofReal (by
      have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
      have : 0 ≤ H - ∑ i, w i := by linarith
      positivity), ENNReal.toReal_natCast] at this
  · have h1 := card_le_vol w hw H
    rw [wvol w hw _ (by linarith)] at h1
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rwa [ENNReal.toReal_ofReal (by
      have hp : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
      have : 0 ≤ H + ∑ i, w i := by linarith
      positivity), ENNReal.toReal_natCast] at this

end PXCS

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology in
theorem solution
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∀ᶠ H : ℝ in atTop,
      ((H - ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) ≤
          ((strictWeightedSimplex w H).card : ℝ) ∧
        ((strictWeightedSimplex w H).card : ℝ) ≤
          ((H + ∑ i, w i) ^ n / ((n.factorial : ℝ) * ∏ i, w i)) :=
  PXCS.sandwich n w hw

-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:39:51.255976+00:00
-- url     : https://prove2.me/submissions/5ced6107-1c54-46d3-894c-a467576c7dd5

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

section

open MeasureTheory Set

namespace PiL4

lemma slice_eq {m : ℕ} (s : Set (Fin (m + 1) → ℝ)) (t : ℝ) :
    Prod.mk t ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) =
      {y : Fin m → ℝ | (Fin.cons t y : Fin (m + 1) → ℝ) ∈ s} := by
  ext y
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl

lemma vol_eq_lintegral {m : ℕ} (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    volume s = ∫⁻ t, volume {y : Fin m → ℝ | (Fin.cons t y : Fin (m + 1) → ℝ) ∈ s} := by
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  rw [← h.measure_preimage_equiv s, Measure.volume_eq_prod, Measure.prod_apply]
  · simp_rw [slice_eq]
  · exact (MeasurableEquiv.measurable _) hs

lemma meas_slice {m : ℕ} (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    Measurable fun t : ℝ => volume {y : Fin m → ℝ | (Fin.cons t y : Fin (m + 1) → ℝ) ∈ s} := by
  have := measurable_measure_prodMk_left (ν := (volume : Measure (Fin m → ℝ)))
    ((MeasurableEquiv.measurable (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm) hs)
  simp_rw [slice_eq] at this
  exact this

theorem box_fubini (m : Nat) (A : Real) (hA : 0 ≤ A) (s : Set (Fin (m + 1) → Real)) (hs : MeasurableSet s) (hbox : s ⊆ {x | ∀ i, x i ∈ Set.Icc (0 : Real) A}) :
    (MeasureTheory.volume s).toReal =
      ∫ t in Set.Icc (0 : Real) A,
        (MeasureTheory.volume {y : Fin m → Real | Fin.cons t y ∈ s}).toReal := by
  rw [vol_eq_lintegral s hs, integral_toReal (meas_slice s hs).aemeasurable]
  · congr 1
    rw [← lintegral_indicator measurableSet_Icc]
    congr 1; ext t
    by_cases ht : t ∈ Icc 0 A
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht]
      convert measure_empty (μ := (volume : Measure (Fin m → ℝ)))
      ext y
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
      intro hy
      exact ht (by simpa using hbox hy 0)
  · refine Filter.Eventually.of_forall fun t => ?_
    refine lt_of_le_of_lt (measure_mono (t := Set.pi univ fun _ => Icc (0:ℝ) A) ?_) ?_
    · intro y hy i _
      simpa using hbox hy i.succ
    · rw [volume_pi_pi]; simp [Real.volume_Icc, ENNReal.prod_lt_top]

theorem normalize {m : Nat} (w : Fin m → Real) (A H : Real) (hw : ∀ i, 0 < w i) (hH : 0 < H) (hcut : (∑ i : Fin m, w i) / H < A)
    (hcard : ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : Real) ≤
      (A * H + ∑ i : Fin m, w i) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i) :
    ((OAI.PiExponent.realWeightedSimplex w (A * H)).card : Real) / H ^ m ≤
      (A + (∑ i : Fin m, w i) / H) ^ m /
        ((Nat.factorial m : Nat) : Real) / ∏ i : Fin m, w i := by
  have hp : 0 < ∏ i, w i := Finset.prod_pos fun i _ => hw i
  have hHm : 0 < H ^ m := pow_pos hH m
  have e : (A + (∑ i : Fin m, w i) / H) ^ m = (A * H + ∑ i : Fin m, w i) ^ m / H ^ m := by
    rw [← div_pow]; congr 1; field_simp
  rw [e, div_le_iff₀ hHm]
  calc _ ≤ _ := hcard
    _ = _ := by field_simp

/-- unit box -/
def box {m : ℕ} (n : Fin m → ℕ) : Set (Fin m → ℝ) :=
  {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1}

lemma box_eq {m : ℕ} (n : Fin m → ℕ) : box n = Set.pi univ fun i => Ico (n i : ℝ) (n i + 1) := by
  ext x; simp [box]

lemma vol_box {m : ℕ} (n : Fin m → ℕ) : volume (box n) = 1 := by
  rw [box_eq, Real.volume_pi_Ico]; simp

lemma box_meas {m : ℕ} (n : Fin m → ℕ) : MeasurableSet (box n) := by
  rw [box_eq]; exact MeasurableSet.univ_pi fun i => measurableSet_Ico

lemma union_lt_top {m : ℕ} (S : Finset (Fin m → ℕ)) : volume (⋃ n ∈ S, box n) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le _ _) ?_
  simp [vol_box]

lemma union_eq {m : ℕ} (S : Finset (Fin m → ℕ)) : volume (⋃ n ∈ S, box n) = S.card := by
  rw [measure_biUnion_finset]
  · simp [vol_box]
  · intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro x hxa hxb
    apply hab
    funext i
    obtain ⟨h1, h2⟩ := hxa i
    obtain ⟨h3, h4⟩ := hxb i
    have e1' : a i < b i + 1 := by exact_mod_cast lt_of_le_of_lt h1 h4
    have e2' : b i < a i + 1 := by exact_mod_cast lt_of_le_of_lt h3 h2
    omega
  · intro a _; exact box_meas a

lemma mem_rws {m : ℕ} {w : Fin m → ℝ} {R : ℝ} {a : Fin m → ℕ} :
    a ∈ OAI.PiExponent.realWeightedSimplex w R ↔
      (∀ i, a i < ⌊R / w i⌋₊ + 1) ∧ ∑ i, w i * (a i : ℝ) ≤ R := by
  simp [OAI.PiExponent.realWeightedSimplex, Fintype.mem_piFinset]

theorem floor_cover {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i}).toReal ≤
      (MeasureTheory.volume (⋃ n ∈ OAI.PiExponent.realWeightedSimplex w R,
        {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1})).toReal := by
  refine ENNReal.toReal_mono (union_lt_top _).ne (measure_mono ?_)
  rintro x ⟨hx0, hxs⟩
  have h0 : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => (hw i).le
  have hle : ∀ i, w i * x i ≤ R := fun i => by
    have := Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (hx0 j))
      (Finset.mem_univ i)
    linarith
  simp only [mem_iUnion, mem_setOf_eq, exists_prop]
  refine ⟨fun i => ⌊x i⌋₊, mem_rws.2 ⟨fun i => ?_, ?_⟩, fun i => ⟨Nat.floor_le (hx0 i), Nat.lt_floor_add_one _⟩⟩
  · apply Nat.lt_succ_of_le
    apply Nat.floor_le_floor
    rw [le_div_iff₀ (hw i), mul_comm]; exact hle i
  · calc ∑ i, w i * (⌊x i⌋₊ : ℝ) ≤ ∑ i, w i * x i :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (Nat.floor_le (hx0 i)) (hw i).le
      _ ≤ R := by linarith

lemma region_lt_top {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i) (C : ℝ) :
    volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ C} < ⊤ := by
  refine lt_of_le_of_lt (measure_mono (t := Set.pi univ fun i => Icc (0:ℝ) (|C| / w i)) ?_) ?_
  · rintro x ⟨hx0, hxs⟩ i _
    refine ⟨hx0 i, ?_⟩
    have := Finset.single_le_sum (f := fun j => w j * x j) (fun j _ => mul_nonneg (hw j).le (hx0 j))
      (Finset.mem_univ i)
    rw [le_div_iff₀ (hw i), mul_comm]
    linarith [le_abs_self C]
  · rw [volume_pi_pi]; simp [Real.volume_Icc, ENNReal.prod_lt_top]

theorem card_le {m : Nat} (w : Fin m → Real) (B : Real) (hw : ∀ i, 0 < w i) (hB : 0 < B) :
    ((OAI.PiExponent.realWeightedSimplex w B).card : Real) ≤
      (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i}).toReal := by
  have h1 := union_eq (OAI.PiExponent.realWeightedSimplex w B)
  have h2 : (⋃ n ∈ OAI.PiExponent.realWeightedSimplex w B, box n) ⊆
      {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ B + ∑ i : Fin m, w i} := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    have hs := (mem_rws.1 ha).2
    refine ⟨fun i => le_trans (Nat.cast_nonneg _) (hxa i).1, ?_⟩
    calc ∑ i, w i * x i ≤ ∑ i, (w i * (a i : ℝ) + w i) := Finset.sum_le_sum fun i _ => by
            nlinarith [(hxa i).2, hw i]
      _ = ∑ i, w i * (a i : ℝ) + ∑ i, w i := Finset.sum_add_distrib
      _ ≤ _ := by linarith
  have := ENNReal.toReal_mono (region_lt_top w hw _).ne (measure_mono h2)
  rw [h1] at this
  simpa using this

end PiL4

end

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) :
    (MeasureTheory.volume {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i}).toReal ≤
      (MeasureTheory.volume (⋃ n ∈ realWeightedSimplex w R,
        {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1})).toReal := by
  apply PiL4.floor_cover <;> assumption

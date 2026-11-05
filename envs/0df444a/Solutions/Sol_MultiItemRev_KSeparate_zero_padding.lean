-- Prove2me | solution 1 for MultiItemRev.KSeparate.zero_padding
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:17:26.562223+00:00
-- url     : https://prove2.me/submissions/dd0ae77d-ffe6-492d-8f5c-08b12eb46324

import Mathlib
import Definitions.Def_MultiItemRev_KSeparate_Model

open MeasureTheory
open scoped NNReal ENNReal

namespace KSepZeroPadAux
open MultiItemRev.Decomp

/-- Padding map `y ↦ (y, 0, …, 0)`. -/
def pad (k j : ℕ) (y : Fin k → ℝ≥0) : Fin (k + j) → ℝ≥0 :=
  Fin.append y (fun _ : Fin j => (0 : ℝ≥0))

/-- Restriction map `x ↦ (x₁, …, x_k)`. -/
def unpad (k j : ℕ) (x : Fin (k + j) → ℝ≥0) : Fin k → ℝ≥0 :=
  fun i => x (Fin.castAdd j i)

lemma measurable_pad (k j : ℕ) : Measurable (pad k j) := by
  refine measurable_pi_iff.mpr fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun l => ?_) i
  · simp only [pad, Fin.append_left]
    exact measurable_pi_apply i
  · simp only [pad, Fin.append_right]
    exact measurable_const

lemma measurable_unpad (k j : ℕ) : Measurable (unpad k j) :=
  measurable_pi_iff.mpr fun i => measurable_pi_apply _

lemma unpad_pad (k j : ℕ) (y : Fin k → ℝ≥0) : unpad k j (pad k j y) = y := by
  funext i
  simp [unpad, pad]

lemma pi_append_zero (k j : ℕ) (ν : Fin k → Measure ℝ≥0) [∀ i, IsProbabilityMeasure (ν i)] :
    Measure.pi (Fin.append ν (fun _ : Fin j => Measure.dirac 0)) =
      (Measure.pi ν).map (pad k j) := by
  have hinst : ∀ i, SigmaFinite (Fin.append ν (fun _ : Fin j => Measure.dirac (0 : ℝ≥0)) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun l => ?_) i
    · rw [Fin.append_left]; infer_instance
    · rw [Fin.append_right]; infer_instance
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply (measurable_pad k j) (MeasurableSet.univ_pi hs), Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  by_cases h : ∀ l : Fin j, (0 : ℝ≥0) ∈ s (Fin.natAdd k l)
  · have hpre : pad k j ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => s (Fin.castAdd j i)) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      constructor
      · intro hy i
        have := hy (Fin.castAdd j i)
        simpa [pad] using this
      · intro hy i
        refine Fin.addCases (fun i => ?_) (fun l => ?_) i
        · simpa [pad] using hy i
        · simpa [pad] using h l
    rw [hpre, Measure.pi_pi]
    have : ∏ l : Fin j, (Measure.dirac (0 : ℝ≥0)) (s (Fin.natAdd k l)) = 1 := by
      refine Finset.prod_eq_one fun l _ => ?_
      rw [Measure.dirac_apply' _ (hs _), Set.indicator_of_mem (h l)]
      rfl
    rw [this, mul_one]
  · push_neg at h
    obtain ⟨l, hl⟩ := h
    have hpre : pad k j ⁻¹' Set.univ.pi s = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_empty_iff_false, iff_false]
      intro hy
      have := hy (Fin.natAdd k l)
      simp [pad] at this
      exact hl this
    have : ∏ l : Fin j, (Measure.dirac (0 : ℝ≥0)) (s (Fin.natAdd k l)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
      rw [Measure.dirac_apply' _ (hs _), Set.indicator_of_notMem hl]
    rw [hpre, this, measure_empty, mul_zero]

lemma sum_pad (k j : ℕ) (a : Fin (k + j) → ℝ) (y : Fin k → ℝ≥0) :
    ∑ i, a i * (pad k j y i : ℝ) = ∑ i, a (Fin.castAdd j i) * (y i : ℝ) := by
  rw [Fin.sum_univ_add]
  simp [pad]

lemma rev_map_pad (k j : ℕ) (μ : Measure (Fin k → ℝ≥0)) :
    Rev (μ.map (pad k j)) = Rev μ := by
  apply le_antisymm
  · unfold Rev
    refine iSup₂_le fun M' hM' => ?_
    let M : Mechanism (Fin k) :=
      ⟨fun y i => M'.q (pad k j y) (Fin.castAdd j i), fun y => M'.s (pad k j y)⟩
    obtain ⟨hF, hIC, hIR, hm⟩ := hM'
    have hM : IsAdmissible M := by
      refine ⟨fun y i => hF _ _, fun y y' => ?_, fun y => ?_,
        hm.comp (measurable_pad k j)⟩
      · have := hIC (pad k j y) (pad k j y')
        unfold buyerPayoff at *
        rw [sum_pad, sum_pad] at this
        exact this
      · have := hIR (pad k j y)
        unfold buyerPayoff at *
        rw [sum_pad] at this
        exact this
    have hrev : expRevenue (μ.map (pad k j)) M' = expRevenue μ M := by
      unfold expRevenue
      rw [lintegral_map (f := fun x => ENNReal.ofReal (M'.s x))
          (ENNReal.measurable_ofReal.comp hm) (measurable_pad k j),
        lintegral_map (f := fun x => ENNReal.ofReal (-M'.s x))
          (ENNReal.measurable_ofReal.comp hm.neg) (measurable_pad k j)]
    rw [hrev]
    exact le_iSup₂ (f := fun (M : Mechanism (Fin k)) (_ : IsAdmissible M) =>
      (expRevenue μ M).toENNReal) M hM
  · unfold Rev
    refine iSup₂_le fun M hM => ?_
    let M' : Mechanism (Fin (k + j)) :=
      ⟨fun x => Fin.append (M.q (unpad k j x)) (fun _ : Fin j => (0 : ℝ)),
        fun x => M.s (unpad k j x)⟩
    have hsum : ∀ x' x : Fin (k + j) → ℝ≥0, ∑ i, M'.q x' i * (x i : ℝ) =
        ∑ i, M.q (unpad k j x') i * (unpad k j x i : ℝ) := by
      intro x' x
      rw [Fin.sum_univ_add]
      simp [M', unpad]
    obtain ⟨hF, hIC, hIR, hm⟩ := hM
    have hM' : IsAdmissible M' := by
      refine ⟨fun x i => ?_, fun x x' => ?_, fun x => ?_,
        hm.comp (measurable_unpad k j)⟩
      · refine Fin.addCases (fun i => ?_) (fun l => ?_) i
        · simp only [M', Fin.append_left]; exact hF _ _
        · simp only [M', Fin.append_right]; norm_num
      · have := hIC (unpad k j x) (unpad k j x')
        unfold buyerPayoff at *
        rw [hsum, hsum]
        exact this
      · have := hIR (unpad k j x)
        unfold buyerPayoff at *
        rw [hsum]
        exact this
    have hrev : expRevenue (μ.map (pad k j)) M' = expRevenue μ M := by
      have hm' : Measurable M'.s := hm.comp (measurable_unpad k j)
      unfold expRevenue
      rw [lintegral_map (f := fun x => ENNReal.ofReal (M'.s x))
          (ENNReal.measurable_ofReal.comp hm') (measurable_pad k j),
        lintegral_map (f := fun x => ENNReal.ofReal (-M'.s x))
          (ENNReal.measurable_ofReal.comp hm'.neg) (measurable_pad k j)]
      simp only [M', unpad_pad]
    rw [← hrev]
    exact le_iSup₂ (f := fun (M : Mechanism (Fin (k + j))) (_ : IsAdmissible M) =>
      (expRevenue (μ.map (pad k j)) M).toENNReal) M' hM'

end KSepZeroPadAux

open KSepZeroPadAux in
theorem solution (k j : ℕ) (ν : Fin k → Measure ℝ≥0)
    [∀ i, IsProbabilityMeasure (ν i)] :
    MultiItemRev.Decomp.Rev (Measure.pi (Fin.append ν (fun _ : Fin j => Measure.dirac 0))) =
      MultiItemRev.Decomp.Rev (Measure.pi ν) := by
  rw [pi_append_zero, rev_map_pad]

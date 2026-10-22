-- Prove2me | solution 1 for MultiItemRev.Decomp.brev_le_rev
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:37:21.136195+00:00
-- url     : https://prove2.me/submissions/409bebbc-88c3-4bd0-9f61-402dc5558f6d

import Mathlib
import Definitions.Def_MultiItemRev_Decomp_Model

set_option autoImplicit false
open MeasureTheory
open scoped NNReal ENNReal
open MultiItemRev.Decomp

theorem solution {ι : Type*} [Fintype ι] [Nonempty ι]
    (μ : Measure (ι → ℝ≥0)) [IsProbabilityMeasure μ] :
    BRev μ ≤ Rev μ := by
  let φ : (ι → ℝ≥0) → (Unit → ℝ≥0) := fun x _ => ∑ i, x i
  have hφ : Measurable φ :=
    measurable_pi_lambda _ fun _ => Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hsum : Measurable (fun x : ι → ℝ≥0 => ∑ i, x i) :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hmap : oneGood (μ.map (fun x => ∑ i, x i)) = μ.map φ := by
    unfold oneGood
    have hg : Measurable (fun t : ℝ≥0 => fun _ : Unit => t) :=
      measurable_pi_lambda _ fun _ => measurable_id
    exact Measure.map_map hg hsum
  unfold BRev Rev1
  rw [hmap]
  unfold Rev
  refine iSup₂_le fun M₁ h₁ => ?_
  obtain ⟨hfe, hic, hir, hms⟩ := h₁
  let M : Mechanism ι := ⟨fun x _ => M₁.q (φ x) (), fun x => M₁.s (φ x)⟩
  have hbp : ∀ x, buyerPayoff M x = buyerPayoff M₁ (φ x) := by
    intro x
    simp only [buyerPayoff, M, φ]
    simp [Finset.mul_sum, NNReal.coe_sum]
  have hqs : ∀ x x' : ι → ℝ≥0, ∑ i, M.q x' i * (x i : ℝ) - M.s x' =
      ∑ i : Unit, M₁.q (φ x') i * ((φ x i : ℝ≥0) : ℝ) - M₁.s (φ x') := by
    intro x x'
    simp only [M, φ]
    simp [Finset.mul_sum, NNReal.coe_sum]
  have hadm : IsAdmissible M := by
    refine ⟨fun x i => hfe (φ x) (), fun x x' => ?_, fun x => ?_, hms.comp hφ⟩
    · rw [hqs, hbp]; exact hic (φ x) (φ x')
    · rw [hbp]; exact hir _
  have hrev : expRevenue μ M = expRevenue (μ.map φ) M₁ := by
    have hm1 : Measurable (fun y : Unit → ℝ≥0 => ENNReal.ofReal (M₁.s y)) :=
      ENNReal.measurable_ofReal.comp hms
    have hm2 : Measurable (fun y : Unit → ℝ≥0 => ENNReal.ofReal (-M₁.s y)) :=
      ENNReal.measurable_ofReal.comp hms.neg
    unfold expRevenue
    rw [lintegral_map hm1 hφ, lintegral_map hm2 hφ]
  refine le_iSup₂_of_le M hadm ?_
  rw [hrev]

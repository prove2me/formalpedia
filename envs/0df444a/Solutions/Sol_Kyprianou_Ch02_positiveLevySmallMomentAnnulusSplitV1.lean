-- Prove2me | solution 1 for Kyprianou.Ch02.positiveLevySmallMomentAnnulusSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:10:47.817192+00:00
-- url     : https://prove2.me/submissions/b4226df4-152f-42cb-ad29-ffabb7bd08d9

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Topology Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (hsmall : IntegrableOn (fun x : ℝ => x) (Set.Ioo 0 r) ν)
    (hband : IntegrableOn (fun x : ℝ => x) (Set.Ico r 1) ν) :
    (∫ x in Set.Ioo (0 : ℝ) 1, x ∂ν) =
      (∫ x in Set.Ioo (0 : ℝ) r, x ∂ν) + ∫ x in Set.Ico r 1, x ∂ν := by
  have hdis : Disjoint (Set.Ioo 0 r) (Set.Ico r 1) := by
    rw [Set.disjoint_left]
    exact fun x hx hy => (not_lt_of_ge hy.1) hx.2
  have hAB : Set.Ioo 0 r ∪ Set.Ico r 1 = Set.Ioo 0 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioo, Set.mem_Ico]
    constructor
    · rintro (h | h) <;> constructor <;> linarith [h.1, h.2]
    · intro h
      by_cases hx : x < r
      · exact Or.inl ⟨h.1, hx⟩
      · exact Or.inr ⟨le_of_not_gt hx, h.2⟩
  rw [← hAB]
  exact setIntegral_union hdis measurableSet_Ico hsmall hband

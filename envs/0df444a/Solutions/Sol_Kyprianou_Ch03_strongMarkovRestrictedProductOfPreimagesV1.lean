-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovRestrictedProductOfPreimagesV1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:40:43.823135+00:00
-- url     : https://prove2.me/submissions/ecb7e2af-83f4-4b8f-b3a9-641f062e8d03

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
theorem _root_.solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (D : Set Omega) (hD : MeasurableSet D)
    (I : Omega → Real) (Y : Omega → (NNReal → Real))
    (nu : Measure (NNReal → Real))
    (hI : AEMeasurable I (P.restrict D))
    (hY : AEMeasurable Y (P.restrict D))
    (hLaw : ∀ S : Set Real, MeasurableSet S →
      MeasurableSet (I ⁻¹' S ∩ D) ∧
      Measure.map Y (P.restrict (I ⁻¹' S ∩ D)) =
        P (I ⁻¹' S ∩ D) • nu) :
    Measure.map (fun w => (I w, Y w)) (P.restrict D) =
      (Measure.map I (P.restrict D)).prod nu := by
  have huniv := (hLaw Set.univ MeasurableSet.univ).2
  rw [Set.preimage_univ, Set.univ_inter] at huniv
  have hIY : AEMeasurable (fun w => (I w, Y w)) (P.restrict D) := hI.prodMk hY
  have key : ∀ (S : Set ℝ) (T : Set (NNReal → ℝ)), MeasurableSet S → MeasurableSet T →
      Measure.map (fun w => (I w, Y w)) (P.restrict D) (S ×ˢ T) = (Measure.map I (P.restrict D)) S * (Measure.map Y (P.restrict D)) T * 1 ∨ True := fun _ _ _ _ => Or.inr trivial
  have hcell : ∀ (S : Set ℝ) (T : Set (NNReal → ℝ)), MeasurableSet S → MeasurableSet T →
      Measure.map (fun w => (I w, Y w)) (P.restrict D) (S ×ˢ T) = P (I ⁻¹' S ∩ D) * nu T := by
    intro S T hS hT
    obtain ⟨hm, hl⟩ := hLaw S hS
    have hY' : AEMeasurable Y (P.restrict (I ⁻¹' S ∩ D)) := hY.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl)
    have h1 : Measure.map Y (P.restrict (I ⁻¹' S ∩ D)) T = P (I ⁻¹' S ∩ D) * nu T := by
      rw [hl]; rfl
    rw [← h1, Measure.map_apply_of_aemeasurable hIY (hS.prod hT), Measure.map_apply_of_aemeasurable hY' hT]
    rw [Measure.restrict_apply₀ (hIY.nullMeasurable (hS.prod hT)), Measure.restrict_apply₀ (hY'.nullMeasurable hT)]
    congr 1
    ext w
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
    tauto
  have hIm : ∀ S : Set ℝ, MeasurableSet S → (Measure.map I (P.restrict D)) S = P (I ⁻¹' S ∩ D) := by
    intro S hS
    rw [Measure.map_apply_of_aemeasurable hI hS, Measure.restrict_apply₀ (hI.nullMeasurable hS)]
  by_cases hD0 : P D = 0
  · have : P.restrict D = 0 := Measure.restrict_eq_zero.2 hD0
    simp [this]
  have hnu : IsProbabilityMeasure nu := by
    refine ⟨?_⟩
    have h := congrArg (fun m : Measure (NNReal → ℝ) => m Set.univ) huniv
    simp only [Measure.smul_apply, smul_eq_mul] at h
    rw [Measure.map_apply_of_aemeasurable hY MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
    exact (ENNReal.mul_right_inj hD0 (measure_ne_top P D)).1 (by rw [mul_one]; exact h.symm)
  symm
  refine Measure.prod_eq fun S T hS hT => ?_
  rw [hcell S T hS hT, hIm S hS]


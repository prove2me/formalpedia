-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanRightMixingSetIntegralV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:20:55.17903+00:00
-- url     : https://prove2.me/submissions/31b7122d-49c7-4dc5-8c9b-8490c102cae9

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_mckeanMarkedIndependentMixing
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (s : ℝ≥0)
    (Y Z : Ω → ℝ)
    (f : ℝ → ℝ) (K : ℝ)
    (hYm : @Measurable Ω ℝ (F s) inferInstance Y)
    (hZm : Measurable Z)
    (hf : Measurable f)
    (hBound : ∀ y, ‖f y‖ ≤ K)
    (hIndep : Indep (MeasurableSpace.comap Z inferInstance) (F s) P) :
    ∀ (A : Set Ω), MeasurableSet[F s] A →
      (∫ ω in A, f (Y ω + Z ω) ∂P) =
        (∫ ω in A, (∫ ξ, f (Y ω + Z ξ) ∂P) ∂P) := by
  classical
  intro A hA
  have hAamb : MeasurableSet A := (F.le s) A hA
  let T : Ω → ℝ × Bool := fun ω => (Y ω, decide (ω ∈ A))
  have hFlag :
      @Measurable Ω Bool (F s) inferInstance
        (fun ω : Ω => decide (ω ∈ A)) := by
    apply measurable_to_bool
    have hpre : ((fun ω : Ω => decide (ω ∈ A)) ⁻¹' {true}) = A := by
      ext ω
      simp
    simpa only [hpre] using hA
  have hTpast :
      @Measurable Ω (ℝ × Bool) (F s) inferInstance T :=
    hYm.prodMk hFlag
  have hT : Measurable T := hTpast.mono (F.le s) le_rfl
  have hInd : IndepFun T Z P := by
    apply (IndepFun_iff_Indep T Z P).2
    exact indep_of_indep_of_le_left hIndep.symm hTpast.comap_le
  have hMarked := Kyprianou.Ch01.mckeanMarkedIndependentMixing
    P T Z f K hT hZm hf hBound hInd
  calc
    (∫ ω in A, f (Y ω + Z ω) ∂P)
        = ∫ ω, if (T ω).2 = true then f ((T ω).1 + Z ω) else 0 ∂P := by
          rw [← integral_indicator hAamb]
          congr 1
          funext ω
          by_cases hw : ω ∈ A <;> simp [T, Set.indicator, hw]
    _ = ∫ ω, if (T ω).2 = true then
          (∫ ξ, f ((T ω).1 + Z ξ) ∂P) else 0 ∂P := hMarked
    _ = (∫ ω in A, (∫ ξ, f (Y ω + Z ξ) ∂P) ∂P) := by
      rw [← integral_indicator hAamb]
      congr 1
      funext ω
      by_cases hw : ω ∈ A <;> simp [T, Set.indicator, hw]

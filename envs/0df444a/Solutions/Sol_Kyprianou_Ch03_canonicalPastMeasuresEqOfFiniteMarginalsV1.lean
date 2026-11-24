-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalPastMeasuresEqOfFiniteMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:25.118514+00:00
-- url     : https://prove2.me/submissions/f3ffe40c-6cd7-44af-9700-cfd22a3654c0

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_canonicalPastCylinderGenerateV1
import Theorems.Thm_Kyprianou_Ch03_canonicalPastCylinderPiSystemV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (Q R : Measure {path : NNReal → ℝ // path 0 = 0}) [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (t : NNReal)
    (hMarg : ∀ I : Finset NNReal, (∀ s ∈ I, s ≤ t) →
      Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) Q =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) R) :
    ∀ A : Set {path : NNReal → ℝ // path 0 = 0}, MeasurableSet[PerfCorrMSQ.natFiltr X t] A → Q A = R A := by
  classical
  have hm (u : NNReal) : Measurable (X u) := by
    have he : X u = fun w => w.val u := funext (hCoordinate u)
    rw [he]
    exact (measurable_pi_apply u).comp measurable_subtype_coe
  have hle : PerfCorrMSQ.natFiltr X t ≤ (inferInstance : MeasurableSpace {path : NNReal → ℝ // path 0 = 0}) :=
    iSup₂_le fun u _ => (hm u).comap_le
  let C : Set (Set {path : NNReal → ℝ // path 0 = 0}) :=
    {A | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E}
  have hgen : PerfCorrMSQ.natFiltr X t = MeasurableSpace.generateFrom C :=
    Kyprianou.Ch03.canonicalPastCylinderGenerateV1 X hCoordinate t
  have hPi : IsPiSystem C := Kyprianou.Ch03.canonicalPastCylinderPiSystemV1 t
  intro A hA
  refine MeasurableSpace.induction_on_inter
    (m := PerfCorrMSQ.natFiltr X t) (C := fun B _ => Q B = R B)
    hgen hPi ?_ ?_ ?_ ?_ A hA
  · simp
  · rintro B ⟨I, hI, E, hE, rfl⟩
    have hr : Measurable (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) := (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I).comp
      (measurable_subtype_coe : Measurable (Subtype.val : {path : NNReal → ℝ // path 0 = 0} → _))
    have hh := congrArg (fun ν : Measure (∀ _ : I, ℝ) => ν E) (hMarg I hI)
    simpa only [Measure.map_apply hr hE] using hh
  · intro B hB hEq
    rw [measure_compl (hle B hB) (measure_ne_top Q B),
      measure_compl (hle B hB) (measure_ne_top R B), measure_univ, measure_univ, hEq]
  · intro g hd hm' he
    have hg : ∀ i, MeasurableSet (g i) := fun i => hle _ (hm' i)
    rw [measure_iUnion hd hg, measure_iUnion hd hg]
    exact tsum_congr he

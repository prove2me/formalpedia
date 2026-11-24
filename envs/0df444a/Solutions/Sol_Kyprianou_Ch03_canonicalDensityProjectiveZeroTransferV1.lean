-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalDensityProjectiveZeroTransferV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:20:02.877881+00:00
-- url     : https://prove2.me/submissions/9e1fcd01-612f-4435-ae75-f9cc7da70f1a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_canonicalProductZeroOriginMarginalsV1
import Theorems.Thm_Kyprianou_Ch03_canonicalPastMeasuresEqOfFiniteMarginalsV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (Z : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hNonneg : ∀ t w, 0 ≤ Z t w)
    (hInt : ∀ t, Integrable (Z t) P)
    (hUnit : ∀ t, (∫ w, Z t w ∂P) = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (Z t) w ∂P) = (∫ w, A.indicator (Z s) w ∂P))
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val)
          (P.withDensity (fun w => ENNReal.ofReal (Z (I.sup id) w)))) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
        Q A = ENNReal.ofReal (∫ w, A.indicator (Z t) w ∂P) := by
  classical
  let M : NNReal → Measure {path : NNReal → ℝ // path 0 = 0} :=
    fun t => P.withDensity (fun w => ENNReal.ofReal (Z t w))
  obtain ⟨Q, hQ, hQm⟩ := Kyprianou.Ch03.canonicalProductZeroOriginMarginalsV1 μ M hProj
  letI := hQ
  have hProb (t : NNReal) : IsProbabilityMeasure (M t) := by
    refine ⟨?_⟩
    dsimp only [M]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hInt t) (ae_of_all _ (hNonneg t)),
      hUnit t, ENNReal.ofReal_one]
  have hm (u : NNReal) : Measurable (X u) := by
    have he : X u = fun w => w.val u := funext (hCoordinate u)
    rw [he]
    exact (measurable_pi_apply u).comp measurable_subtype_coe
  have hle (u : NNReal) : PerfCorrMSQ.natFiltr X u ≤ (inferInstance : MeasurableSpace {path : NNReal → ℝ // path 0 = 0}) :=
    iSup₂_le fun v _ => (hm v).comap_le
  have hApply (u : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0})
      (hA : MeasurableSet A) : M u A = ENNReal.ofReal (∫ w, A.indicator (Z u) w ∂P) := by
    dsimp only [M]
    rw [withDensity_apply _ hA, integral_indicator hA]
    exact (ofReal_integral_eq_lintegral_ofReal (hInt u).integrableOn
      (ae_of_all _ (hNonneg u))).symm
  refine ⟨Q, measure_univ, ?_⟩
  intro t A hA
  letI := hProb t
  rw [← hApply t A (hle t A hA)]
  apply Kyprianou.Ch03.canonicalPastMeasuresEqOfFiniteMarginalsV1 Q (M t) X hCoordinate t _ A hA
  intro I hI
  rw [hQm I]
  have hr : Measurable (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) := (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I).comp
    (measurable_subtype_coe : Measurable (Subtype.val : {path : NNReal → ℝ // path 0 = 0} → _))
  have hrF : Measurable[PerfCorrMSQ.natFiltr X (I.sup id)]
      (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) := by
    refine @measurable_pi_lambda {path : NNReal → ℝ // path 0 = 0} I (fun _ => ℝ)
      (PerfCorrMSQ.natFiltr X (I.sup id)) _ _ fun i => ?_
    have hx : Measurable[PerfCorrMSQ.natFiltr X (I.sup id)] (X i.1) :=
      measurable_iff_comap_le.mpr (le_iSup₂_of_le i.1 (Finset.le_sup (f := id) i.2) le_rfl)
    rw [show X i.1 = (fun w => w.val i.1) from funext (hCoordinate i.1)] at hx
    exact hx
  ext E hE
  rw [Measure.map_apply hr hE, Measure.map_apply hr hE,
    hApply _ _ (hr hE), hApply _ _ (hr hE),
    hCons (I.sup id) t (Finset.sup_le fun s hs => hI s hs) _ (hrF hE)]

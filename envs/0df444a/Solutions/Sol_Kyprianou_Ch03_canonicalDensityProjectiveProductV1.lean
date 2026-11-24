-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalDensityProjectiveProductV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:24:24.136932+00:00
-- url     : https://prove2.me/submissions/6e4dbc76-7ef1-4b93-a736-26c07eb26858

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_levy_foundations_kolmogorovExtension_exists
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
      (∫ w, A.indicator (Z t) w ∂P) = (∫ w, A.indicator (Z s) w ∂P)) :
    ∃ μ : Measure (NNReal → ℝ), IsProbabilityMeasure μ ∧
      ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val)
          (P.withDensity (fun w => ENNReal.ofReal (Z (I.sup id) w))) := by
  classical
  let Ptilt : NNReal → Measure {path : NNReal → ℝ // path 0 = 0} :=
    fun t => P.withDensity (fun w => ENNReal.ofReal (Z t w))
  have hProb (t : NNReal) : IsProbabilityMeasure (Ptilt t) := by
    refine ⟨?_⟩
    dsimp only [Ptilt]
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
      (hA : MeasurableSet A) : Ptilt u A = ENNReal.ofReal (∫ w, A.indicator (Z u) w ∂P) := by
    dsimp only [Ptilt]
    rw [withDensity_apply _ hA, integral_indicator hA]
    exact (ofReal_integral_eq_lintegral_ofReal (hInt u).integrableOn
      (ae_of_all _ (hNonneg u))).symm
  have hEq (s t : NNReal) (hst : s ≤ t) (A : Set {path : NNReal → ℝ // path 0 = 0})
      (hA : MeasurableSet[PerfCorrMSQ.natFiltr X s] A) : Ptilt t A = Ptilt s A := by
    rw [hApply t A (hle s A hA), hApply s A (hle s A hA), hCons s t hst A hA]
  let Qfam : ∀ I : Finset NNReal, Measure (∀ _ : I, ℝ) :=
    fun I => (Ptilt (I.sup id)).map (fun w => I.restrict w.val)
  have hmap (I : Finset NNReal) :
      Measurable (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) :=
    (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) I).comp measurable_subtype_coe
  have hmapF (I : Finset NNReal) : Measurable[PerfCorrMSQ.natFiltr X (I.sup id)]
      (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) := by
    refine @measurable_pi_lambda {path : NNReal → ℝ // path 0 = 0} I (fun _ => ℝ)
      (PerfCorrMSQ.natFiltr X (I.sup id)) _ _ fun i => ?_
    have hx : Measurable[PerfCorrMSQ.natFiltr X (I.sup id)] (X i.1) :=
      measurable_iff_comap_le.mpr (le_iSup₂_of_le i.1 (Finset.le_sup (f := id) i.2) le_rfl)
    rw [show X i.1 = (fun w => w.val i.1) from funext (hCoordinate i.1)] at hx
    exact hx
  let pf : LevyFoundations.ProjectiveFamily NNReal (fun _ : NNReal => ℝ) := {
    measure := Qfam
    prob := fun I =>
      letI := hProb (I.sup id)
      Measure.isProbabilityMeasure_map (hmap I).aemeasurable
    consistent := by
      intro I J hJI
      ext E hE
      have hrm := Finset.measurable_restrict₂ (X := fun _ : NNReal => ℝ) hJI
      symm
      change (Measure.map (Finset.restrict₂ (π := fun _ : NNReal => ℝ) hJI) (Qfam I)) E = Qfam J E
      rw [Measure.map_apply hrm hE]
      dsimp only [Qfam]
      rw [Measure.map_apply (hmap I) (hrm hE), Measure.map_apply (hmap J) hE]
      exact hEq (J.sup id) (I.sup id) (Finset.sup_mono hJI) _ ((hmapF J) hE)
  }
  obtain ⟨μ, hProj⟩ := levy_foundations_kolmogorovExtension_exists pf
  have hμ : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    have h := congrArg (fun ν : Measure (∀ _ : (∅ : Finset NNReal), ℝ) => ν Set.univ) (hProj ∅)
    have hu : μ Set.univ = Qfam ∅ Set.univ := by
      simpa [Measure.map_apply (Finset.measurable_restrict (X := fun _ : NNReal => ℝ) ∅)
        MeasurableSet.univ] using h
    rw [hu]
    haveI := pf.prob ∅
    exact measure_univ
  exact ⟨μ, hμ, hProj⟩

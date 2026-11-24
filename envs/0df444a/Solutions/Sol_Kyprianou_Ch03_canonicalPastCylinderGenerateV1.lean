-- Prove2me | solution 1 for Kyprianou.Ch03.canonicalPastCylinderGenerateV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:24:35.451161+00:00
-- url     : https://prove2.me/submissions/63b8f43b-f43d-4050-9c89-52ee7193d6d9

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (t : NNReal) :
    PerfCorrMSQ.natFiltr X t = MeasurableSpace.generateFrom
      {A : Set {path : NNReal → ℝ // path 0 = 0} | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E} := by
  classical
  let C : Set (Set {path : NNReal → ℝ // path 0 = 0}) :=
    {A | ∃ (I : Finset NNReal) (_ : ∀ s ∈ I, s ≤ t)
      (E : Set (∀ _ : I, ℝ)), MeasurableSet E ∧ A = (fun w => I.restrict w.val) ⁻¹' E}
  have hgen : PerfCorrMSQ.natFiltr X t = MeasurableSpace.generateFrom C := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun u hu => ?_
      rintro A ⟨B, hB, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ?_
      let I : Finset NNReal := {u}
      have hI : ∀ s ∈ I, s ≤ t := fun s hs => by
        rw [Finset.mem_singleton.mp hs]
        exact hu
      let E : Set (∀ _ : I, ℝ) := (fun g => g ⟨u, Finset.mem_singleton_self u⟩) ⁻¹' B
      have hE : MeasurableSet E := (measurable_pi_apply (⟨u, Finset.mem_singleton_self u⟩ : I)) hB
      refine ⟨I, hI, E, hE, ?_⟩
      ext w
      simp only [mem_preimage, E, hCoordinate]
      rfl
    · refine MeasurableSpace.generateFrom_le ?_
      rintro A ⟨I, hI, E, hE, rfl⟩
      have hres : Measurable[PerfCorrMSQ.natFiltr X t]
          (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val) := by
        refine @measurable_pi_lambda {path : NNReal → ℝ // path 0 = 0} I (fun _ => ℝ)
          (PerfCorrMSQ.natFiltr X t) _ _ fun i => ?_
        have hx : Measurable[PerfCorrMSQ.natFiltr X t] (X i.1) :=
          measurable_iff_comap_le.mpr (le_iSup₂_of_le i.1 (hI i.1 i.2) le_rfl)
        rw [show X i.1 = (fun w => w.val i.1) from funext (hCoordinate i.1)] at hx
        exact hx
      exact hres hE
  exact hgen

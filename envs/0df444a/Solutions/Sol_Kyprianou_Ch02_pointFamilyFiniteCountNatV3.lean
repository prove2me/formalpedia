-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyFiniteCountNatV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:33:06.608828+00:00
-- url     : https://prove2.me/submissions/4a9d9dcc-85c5-49fb-8bd2-3b1c4e5d82ca

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_pointFamilyFinitePRMCoreCh02V1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ∃ n : ℕ,
         ProbabilityTheory.poissonRandomMeasure K Y ω A = (n : ENNReal) := by
  classical
  intro A hA hfin
  obtain ⟨hmeasAll, hlawAll, _⟩ :=
    Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1 P m K Y hd
  let f : Ω → ENNReal := fun ω => ProbabilityTheory.poissonRandomMeasure K Y ω A
  let s : Set ENNReal := Set.range (Nat.cast : ℕ → ENNReal)
  have hs : MeasurableSet s := (Set.countable_range _).measurableSet
  have hf : Measurable f := hmeasAll A hA
  have hRng : ∀ᵐ y ∂((ProbabilityTheory.poissonMeasure (m A).toNNReal).map
      (Nat.cast : ℕ → ENNReal)), y ∈ s := by
    apply (ae_map_iff (measurable_from_top.aemeasurable) hs).2
    exact Filter.Eventually.of_forall fun n => ⟨n, rfl⟩
  have hlaw := hlawAll A hA hfin
  change P.map f = _ at hlaw
  rw [← hlaw] at hRng
  have hgood : ∀ᵐ ω ∂P, f ω ∈ s :=
    (ae_map_iff hf.aemeasurable hs).1 hRng
  filter_upwards [hgood] with ω hω
  obtain ⟨n, hn⟩ := hω
  exact ⟨n, hn.symm⟩

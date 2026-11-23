-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyPRMResidualV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:29:46.05427+00:00
-- url     : https://prove2.me/submissions/e066e64d-32d1-41ca-958a-22378fae1248

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_pointFamilyFiniteCountNatV3
import Theorems.Thm_Kyprianou_Ch02_pointFamilyInfiniteCountTopV3
import Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableCountsIndependentV3

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    (∀ A : Set E, MeasurableSet A → m A < ⊤ →
       ∀ᵐ ω ∂P, ∃ n : ℕ, ProbabilityTheory.poissonRandomMeasure K Y ω A = (n : ENNReal)) ∧
    (∀ A : Set E, MeasurableSet A → m A = ⊤ →
       ∀ᵐ ω ∂P, ProbabilityTheory.poissonRandomMeasure K Y ω A = ⊤) ∧
    (∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P) := by
  exact ⟨Kyprianou.Ch02.pointFamilyFiniteCountNatV3 P m K Y hd,
    Kyprianou.Ch02.pointFamilyInfiniteCountTopV3 P m K Y hd,
    Kyprianou.Ch02.pointFamilyCountableCountsIndependentV3 P m K Y hd⟩

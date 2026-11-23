-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyCountableFiniteIntensityIndependentV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:37:57.551581+00:00
-- url     : https://prove2.me/submissions/70380949-3202-4621-b0e9-347d31f42495

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P)
    {ι : Type} [Countable ι] (A : ι → Set E)
    (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdis : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ProbabilityTheory.iIndepFun
      (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P := by
  classical
  apply (ProbabilityTheory.iIndepFun_iff_finset).2
  intro s
  have hind :
      ProbabilityTheory.iIndepFun
        (fun (i : s) (ω : Ω) =>
          ProbabilityTheory.poissonRandomMeasure K Y ω (A i.1)) P := by
    apply ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply hd
    · intro i
      exact hA i.1
    · intro i
      exact hfin i.1
    · intro i j hij
      exact hdis (Subtype.coe_injective.ne hij)
  exact hind

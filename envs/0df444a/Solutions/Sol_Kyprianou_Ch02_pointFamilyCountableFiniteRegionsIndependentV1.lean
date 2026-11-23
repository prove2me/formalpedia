-- Prove2me | solution 1 for Kyprianou.Ch02.pointFamilyCountableFiniteRegionsIndependentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:55:44.562239+00:00
-- url     : https://prove2.me/submissions/74ee5428-7343-41fc-8d7c-59d77ab28124

import Mathlib.Probability.Independence.Basic
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_iIndepFun_poissonRandomMeasure_apply
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : IsPoissonPointFamily K Y m P)
    {ι : Type} [Countable ι] (B : ι → Set E)
    (hm : ∀ i, MeasurableSet (B i))
    (hf : ∀ i, m (B i) < ⊤)
    (hdj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    iIndepFun (fun i ω => poissonRandomMeasure K Y ω (B i)) P := by
  classical
  apply iIndepFun_iff_finset.mpr
  intro s
  let C : s → Set E := fun i => B i.1
  have hc : ∀ i, MeasurableSet (C i) := fun i => hm i
  have hf' : ∀ i, m (C i) < ⊤ := fun i => hf i
  have hd' : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    exact hdj (fun h => hij (Subtype.ext h))
  have hrestrict :
      s.restrict (fun i ω => poissonRandomMeasure K Y ω (B i)) =
        (fun i ω => poissonRandomMeasure K Y ω (B i.1)) := by
    rfl
  rw [hrestrict]
  exact ProbabilityTheory.iIndepFun_poissonRandomMeasure_apply
    (ι := s) hd hc hf' hd'

-- Prove2me | solution 2 for Kyprianou.Ch02.pointFamilyCountableCountsIndependentV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:53:44.233347+00:00
-- url     : https://prove2.me/submissions/bff5ec5f-de97-4e71-bb54-88dba7752332

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_Kyprianou_Ch02_pointFamilyCountableFiniteRegionsIndependentV1
import Theorems.Thm_Kyprianou_Ch02_independentAeCutoffV1
import Theorems.Thm_Kyprianou_Ch02_finiteIntensityRegionCutoffV1
import Theorems.Thm_Kyprianou_Ch02_pointFamilyInfiniteCountTopV3
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (K : ℕ → Ω → ℕ) (Y : ℕ → ℕ → Ω → E)
    (hd : ProbabilityTheory.IsPoissonPointFamily K Y m P) :
    ∀ {ι : Type} [Countable ι] (A : ι → Set E),
       (∀ i, MeasurableSet (A i)) →
       Pairwise (fun i j => Disjoint (A i) (A j)) →
       ProbabilityTheory.iIndepFun
         (fun i (ω : Ω) => ProbabilityTheory.poissonRandomMeasure K Y ω (A i)) P := by
  classical
  intro ι _ A hmeas hdisj
  let B : ι → Set E := fun i => if m (A i) < ⊤ then A i else ∅
  obtain ⟨hBmeas, hBfin, hBdisj⟩ :=
    Kyprianou.Ch02.finiteIntensityRegionCutoffV1 m A hmeas hdisj
  have hB := Kyprianou.Ch02.pointFamilyCountableFiniteRegionsIndependentV1 P m K Y hd B hBmeas hBfin hBdisj
  have hEq : ∀ i, (fun ω : Ω => poissonRandomMeasure K Y ω (A i)) =ᵐ[P]
      (fun ω : Ω => if m (A i) < ⊤ then poissonRandomMeasure K Y ω (B i)
        else (⊤ : ENNReal)) := by
    intro i
    by_cases hi : m (A i) < ⊤
    · simp [B, hi]
    · have hinf : m (A i) = ⊤ := le_antisymm le_top (le_of_not_gt hi)
      filter_upwards [
        Kyprianou.Ch02.pointFamilyInfiniteCountTopV3 P m K Y hd
          (A i) (hmeas i) hinf
      ] with ω hw
      simpa [B, hi] using hw
  exact Kyprianou.Ch02.independentAeCutoffV1 P (fun i => m (A i) < ⊤)
    (fun i ω => poissonRandomMeasure K Y ω (B i))
    (fun i ω => poissonRandomMeasure K Y ω (A i)) hB hEq

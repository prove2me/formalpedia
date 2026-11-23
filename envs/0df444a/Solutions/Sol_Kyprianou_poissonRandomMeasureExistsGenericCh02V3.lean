-- Prove2me | solution 1 for Kyprianou.poissonRandomMeasureExistsGenericCh02V3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:17:02.366613+00:00
-- url     : https://prove2.me/submissions/3d22aa6a-d3fb-407f-afb5-09ef39316bdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Theorems.Thm_ProbabilityTheory_exists_isPoissonPointFamily
import Theorems.Thm_Kyprianou_Ch02_pointFamilyFinitePRMCoreCh02V1
import Theorems.Thm_Kyprianou_Ch02_pointFamilyPRMResidualV3
import Theorems.Thm_Kyprianou_Ch02_emptyMarkPRMExistsV3

open MeasureTheory ProbabilityTheory Kyprianou
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    (E : Type) [MeasurableSpace E] (m : Measure E) [SigmaFinite m] :
    ∃ (Ω : Type) (measΩ : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := measΩ
      ∃ (P : Measure Ω) (probP : IsProbabilityMeasure P),
        letI : IsProbabilityMeasure P := probP
        ∃ N : Ω → Measure E,
          (∀ (A : Set E), MeasurableSet A →
            Measurable (fun ω => N ω A)) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            ∀ᵐ ω ∂P, ∃ n : ℕ, N ω A = n) ∧
          (∀ (A : Set E), MeasurableSet A → m A < ⊤ →
            P.map (fun ω => N ω A) =
              (ProbabilityTheory.poissonMeasure (m A).toNNReal).map
                (Nat.cast : ℕ → ENNReal)) ∧
          (∀ (A : Set E), MeasurableSet A → m A = ⊤ →
            ∀ᵐ ω ∂P, N ω A = ⊤) ∧
          (∀ {ι : Type} [Countable ι] (A : ι → Set E),
            (∀ i, MeasurableSet (A i)) →
            Pairwise (fun i j => Disjoint (A i) (A j)) →
            ProbabilityTheory.iIndepFun (fun i (ω : Ω) => N ω (A i)) P)
 := by
  classical
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    obtain ⟨Ω, mΩ, P, K, Y, hP, hd⟩ :=
      ProbabilityTheory.exists_isPoissonPointFamily m
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    obtain ⟨hmeas, hlaw, hfinite⟩ :=
      Kyprianou.Ch02.pointFamilyFinitePRMCoreCh02V1 P m K Y hd
    obtain ⟨hnat, hinfinite, hind⟩ :=
      Kyprianou.Ch02.pointFamilyPRMResidualV3 P m K Y hd
    exact ⟨Ω, mΩ, P, hP, ProbabilityTheory.poissonRandomMeasure K Y,
      hmeas, hnat, hlaw, hinfinite, hind⟩
  · exact Kyprianou.Ch02.emptyMarkPRMExistsV3 E m hE

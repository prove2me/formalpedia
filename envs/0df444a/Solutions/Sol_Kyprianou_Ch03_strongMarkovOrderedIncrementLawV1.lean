-- Prove2me | solution 1 for Kyprianou.Ch03.strongMarkovOrderedIncrementLawV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:24:21.978298+00:00
-- url     : https://prove2.me/submissions/13e6b915-ec69-41a8-a5d4-717c76f51717

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch03_strongMarkovShiftedPrefixRectanglesV1
import Theorems.Thm_Kyprianou_Ch03_strongMarkovFiniteVectorLawOfPrefixRectanglesV1
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hAdapt : ∀ t : NNReal, Measurable[F t] (X t))
    (hOne : ∀ (s t : NNReal), s ≤ t → ∀ (A : Set Omega), MeasurableSet[F s] A →
      ∀ (C : Set Real), MeasurableSet C →
      P (A ∩ {w | X t w - X s w ∈ C}) =
        P A * P {w | X t w - X s w ∈ C})
    (hX : IsLevyProcess X P)
    (s : NNReal) (A : Set Omega) (hA : MeasurableSet[F s] A)
    (t : ℕ → NNReal) (ht : Monotone t) (ht0 : t 0 = 0) (n : ℕ) :
    Measure.map (fun w : Omega => fun i : Fin n =>
      X (s+t (i.val+1)) w - X (s+t i.val) w) (P.restrict A) =
    P A • Measure.map (fun w : Omega => fun i : Fin n =>
      X (t (i.val+1)) w - X (t i.val) w) P := by
  classical
  let U : Omega → (Fin n → ℝ) := fun w i => X (s+t (i.val+1)) w - X (s+t i.val) w
  let V : Omega → (Fin n → ℝ) := fun w i => X (t (i.val+1)) w - X (t i.val) w
  have hm (u : NNReal) : Measurable (X u) := (hAdapt u).mono (F.le u) le_rfl
  have hU : Measurable U := measurable_pi_iff.mpr (fun i => (hm _).sub (hm _))
  have hV : Measurable V := measurable_pi_iff.mpr (fun i => (hm _).sub (hm _))
  change Measure.map U (P.restrict A) = P A • Measure.map V P
  apply Kyprianou.Ch03.strongMarkovFiniteVectorLawOfPrefixRectanglesV1 P A n U V hU hV
  intro C hC
  exact Kyprianou.Ch03.strongMarkovShiftedPrefixRectanglesV1 P F X hAdapt hOne hX
    s A hA t ht ht0 C hC n

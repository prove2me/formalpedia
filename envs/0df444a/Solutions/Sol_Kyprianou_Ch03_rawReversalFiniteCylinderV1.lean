-- Prove2me | solution 1 for Kyprianou.Ch03.rawReversalFiniteCylinderV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:24:45.738875+00:00
-- url     : https://prove2.me/submissions/c197ffba-c21e-493b-8bfe-d81125a77a67
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_finiteCylinderOfOrderedGridLawsV1
import Theorems.Thm_Kyprianou_Ch03_finiteZeroBasedVectorLawOfReverseDifferencesV1
import Theorems.Thm_Kyprianou_Ch03_levyReflectedIncrementVectorLawV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t)
    (J : Finset {s : NNReal // s <= t})
    (B : {s : NNReal // s <= t} -> Set Real)
    (hB : ∀ i ∈ J, MeasurableSet (B i)) :
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} =>
      X (t - (s : NNReal)) omega - X t omega) ⁻¹'
        Set.pi (J : Set {s : NNReal // s <= t}) B) =
    P ((fun omega : Omega => fun s : {s : NNReal // s <= t} =>
      -(X (s : NNReal) omega)) ⁻¹'
        Set.pi (J : Set {s : NNReal // s <= t}) B) := by
  have hc := Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX
  let F (s : NNReal) (ω : Omega) := X (t - s) ω - X t ω
  let G (s : NNReal) (ω : Omega) := -(X s ω)
  have hF (s : NNReal) : AEMeasurable (F s) P := (hc _).sub (hc _)
  have hG (s : NNReal) : AEMeasurable (G s) P := (hc _).neg
  refine Kyprianou.Ch03.finiteCylinderOfOrderedGridLawsV1 P t F G hF hG ?_ J B hB
  intro n q hq h0 hqt
  refine Kyprianou.Ch03.finiteZeroBasedVectorLawOfReverseDifferencesV1 P n
    (fun ω i => F (q i) ω) (fun ω i => G (q i) ω) ?_ ?_ ?_ ?_ ?_
  · exact aemeasurable_pi_iff.mpr fun i => hF _
  · exact aemeasurable_pi_iff.mpr fun i => hG _
  · intro ω; simp [F, h0]
  · intro ω; simp [G, h0, hX.start_zero]
  · have eF : (fun ω : Omega => fun i : Fin n =>
        F (q i.castSucc) ω - F (q i.succ) ω) =
        (fun ω : Omega => fun i : Fin n =>
          X (t - q i.castSucc) ω - X (t - q i.succ) ω) := by
      funext ω i
      dsimp [F]
      ring
    have eG : (fun ω : Omega => fun i : Fin n =>
        G (q i.castSucc) ω - G (q i.succ) ω) =
        (fun ω : Omega => fun i : Fin n =>
          X (q i.succ) ω - X (q i.castSucc) ω) := by
      funext ω i
      dsimp [G]
      ring
    rw [eF, eG]
    exact Kyprianou.Ch03.levyReflectedIncrementVectorLawV1 P X hX t n q hq hqt

-- Prove2me | solution 1 for Kyprianou.Ch04.bvRightTruncationTailBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T00:30:01.158461+00:00
-- url     : https://prove2.me/submissions/b57f8071-5bf0-4255-bfdf-ad2b33f3be5b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_bvSummableDominatedFiniteTailV1
import Theorems.Thm_Kyprianou_Ch04_bvHorizonRightJumpSeriesV1
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
set_option autoImplicit false
open Kyprianou.Ch04

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (X Xleft : NNReal → Omega → Real) (omega : Omega) (c : Real)
    (hRep : forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + c * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega))
    (t : NNReal) :
    let j : Set.Ioc (0 : NNReal) t → ℝ := fun s => X s omega - Xleft s omega
    let P : Finset (Set.Ioc (0 : NNReal) t) → NNReal → ℝ :=
      fun S u => X 0 omega + c * (u : ℝ) + ∑ s ∈ S, if (s : NNReal) ≤ u then j s else 0
    ∀ (S : Finset (Set.Ioc (0 : NNReal) t)) (u : NNReal), u ≤ t →
      |X u omega - P S u| ≤ (∑' s, |j s|) - ∑ s ∈ S, |j s| := by
  classical
  intro j P S u hu
  have hseries := Kyprianou.Ch04.bvHorizonRightJumpSeriesV1
    (fun s => X s omega - Xleft s omega) u t hu
  have hX := (hRep u).2
  rw [hseries] at hX
  let g : Set.Ioc (0 : NNReal) t → ℝ := fun s => if (s : NNReal) ≤ u then j s else 0
  have hg : ∀ s, |g s| ≤ |j s| := by
    intro s
    by_cases hs : (s : NNReal) ≤ u <;> simp [g, hs]
  have h := Kyprianou.Ch04.bvSummableDominatedFiniteTailV1
    g (fun s => |j s|) (hRep t).1 hg S
  have heq : X u omega - P S u = (∑' s, g s) - ∑ s ∈ S, g s := by
    rw [hX]
    change X 0 omega + c * (u : ℝ) + (∑' s, g s) -
      (X 0 omega + c * (u : ℝ) + ∑ s ∈ S, g s) = _
    ring
  rw [heq]
  exact h
